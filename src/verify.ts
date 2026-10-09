/**
 * The verification driver (specification 6.5, milestone 7).
 *
 * `verify(path, source, options)` runs the whole pipeline for one file:
 *
 *   lex → find annotated functions → parse → cross-check against Bun → fragment check →
 *   SSA → spec resolution (imports are *parsed*, never executed) → elaborate → certify →
 *   kernel check
 *
 * and returns per-function verdicts, per-obligation statuses, located diagnostics, the
 * imported declarations that were admitted, and an **injection plan** for milestone 8 (this
 * module never edits or runs the user's code).
 *
 * A function is `certified` only when the kernel accepted its complete term.  A function
 * whose fragment contains an error is `rejected` and skipped.  A function nothing can be
 * said about (an internal failure, a loop in part A) is `failed`.  A function Z3 proved but
 * the kernel did not certify is `smt-only`: it is not added to the environment, and in
 * lenient mode its spec is still admitted as an `external` declaration, with every caller
 * marked as depending on an uncertified function.
 */
import {
  hasErrors,
  sortDiagnostics,
  spanContains,
  type Diagnostic,
  type DiagnosticKind,
  type Span,
} from "./diagnostics";
import * as K from "./kernel/index";
import { elaborateFunction, type ObligationOutcome, type FunctionStatus } from "./extract/elaborate";
import { extractFile, type FunctionIR, type ImportedSpec } from "./extract/fragment";
import { contentHash, SpecResolver } from "./extract/specs";
import { parseFile } from "./syntax/parser";
import type { FnDecl } from "./syntax/ast";
import { tagsNamed } from "./syntax/jsdoc";
import * as z3 from "./vc/z3";

/** A function's verdict: the elaborator's statuses plus `rejected` for a fragment error. */
export type Verdict = FunctionStatus | "rejected";

/** What a planned runtime check is: an obligation kind, a `@pre` entry check, or a guard. */
export type InjectionKind = DiagnosticKind | "pre" | "guard";

export interface FunctionVerdict {
  readonly name: string;
  readonly exported: boolean;
  readonly span: Span;
  readonly status: Verdict;
  readonly certified: boolean;
  readonly obligations: readonly ObligationOutcome[];
  /** Imported or local functions this one used although they are not certified. */
  readonly dependsOnUncertified: readonly string[];
}

/** One runtime check milestone 8 has to inject. */
export interface InjectionRecord {
  readonly function: string;
  readonly exported: boolean;
  /** The obligation kind, `pre` for an entry precondition, or `guard` for a boundary guard. */
  readonly kind: InjectionKind;
  readonly span: Span;
  /** The check as written, for `PreconditionError`/`PostconditionError`. */
  readonly specText: string;
  /** True when the kernel certified the obligation this check comes from. */
  readonly certified: boolean;
  /** A `@pre` tag of this function (checked at entry). */
  readonly isPrecondition: boolean;
  /** A boundary type guard for an exported parameter. */
  readonly isBoundaryGuard: boolean;
  /** The parameter a guard or `@pre` concerns, when there is one. */
  readonly param?: string;
  /** The obligation site, when the record comes from one. */
  readonly siteId?: number;
}

/** An imported function whose spec was admitted as a kernel `external` declaration. */
export interface ExternalUse {
  readonly name: string;
  readonly file: string;
  /** sha256 of the imported file the spec was read from. */
  readonly hash: string;
  /** Whether the imported function is certified in its own file, when that is known. */
  readonly certified: boolean | "unknown";
}

export interface VerifyResult {
  readonly path: string;
  readonly strict: boolean;
  /** No failure, and (in strict mode) no `smt-only` obligation and no uncertified callee. */
  readonly ok: boolean;
  readonly functions: readonly FunctionVerdict[];
  readonly diagnostics: readonly Diagnostic[];
  readonly plan: readonly InjectionRecord[];
  readonly externals: readonly ExternalUse[];
  /** Names of axiom declarations used; always `[]` for a verified file. */
  readonly axioms: readonly string[];
  /** The environment after the file was verified. */
  readonly env: K.Env;
}

export interface VerifyOptions {
  /** Strict mode: an `smt-only` obligation or an uncertified callee fails the file. */
  readonly strict?: boolean;
  readonly timeoutMs?: number;
  /** An environment to extend; defaults to `K.emptyEnv()`. */
  readonly env?: K.Env;
  /** File reader for imported specs and for `verifyImports`; defaults to `node:fs`. */
  readonly readFile?: (path: string) => string;
  /** A pre-built spec resolver, so several files share one import cache. */
  readonly resolver?: SpecResolver;
  /**
   * Verify the imported files too, so a caller of an uncertified import can be marked.
   * Off by default: one file is verified at a time.
   */
  readonly verifyImports?: boolean;
  /**
   * Whether an SMT solver is available.  Defaults to `z3.isAvailable()`: without `libz3`,
   * every obligation is reported as `smt-only` — not discharged, so a runtime check is
   * needed — instead of failing with a solver error (section 4.4).  Pass `true` explicitly
   * to see the solver's own error messages.
   */
  readonly solver?: boolean;
}

/**
 * Verify one file.  Never throws: any internal failure becomes a located `internal`
 * diagnostic and a `failed` verdict for the function it happened in.
 */
export function verify(path: string, source: string, options: VerifyOptions = {}): VerifyResult {
  const strict = options.strict === true;
  const solver = options.solver ?? z3.isAvailable();
  let env = options.env ?? K.emptyEnv();
  const resolver = options.resolver ?? new SpecResolver(options.readFile);
  const parsed = parseFile(path, source);
  const hash = contentHash(source);
  const diagnostics: Diagnostic[] = [];
  const verdicts: FunctionVerdict[] = [];
  const plan: InjectionRecord[] = [];
  const externals: ExternalUse[] = [];

  let ir;
  try {
    ir = extractFile(path, source, { resolver, parsed });
  } catch (error) {
    diagnostics.push({
      kind: "internal",
      severity: "error",
      span: { file: path, line: 1, col: 1, offset: 0 },
      message: `the extractor failed on ${path}: ${error instanceof Error ? error.message : String(error)}`,
    });
    return {
      path,
      strict,
      ok: false,
      functions: [],
      diagnostics: sortDiagnostics(diagnostics),
      plan: [],
      externals: [],
      axioms: K.axiomsUsed(env),
      env,
    };
  }
  diagnostics.push(...ir.diagnostics);

  // --- imported specs: parsed files only, admitted as `external` declarations -------------
  const uncertified = new Set<string>();
  if (options.verifyImports === true) {
    for (const spec of allImports(ir.functions)) {
      const status = importCertified(spec, options);
      if (status === false) uncertified.add(spec.name);
      externals.push({ name: spec.name, file: spec.file, hash: spec.hash, certified: status });
    }
  } else {
    for (const spec of allImports(ir.functions)) {
      externals.push({ name: spec.name, file: spec.file, hash: spec.hash, certified: "unknown" });
    }
  }
  for (const spec of allImports(ir.functions)) {
    const added = K.addDecl(env, spec.decl);
    if (added.ok) env = added.value;
    else if (!env.decls.has(spec.name)) {
      diagnostics.push({
        kind: "internal",
        severity: "error",
        span: importSpan(spec),
        message: `the imported declaration \`${spec.name}\` was rejected: ${K.formatKernelError(added.error)}`,
      });
    }
  }

  // --- which functions are rejected outright? --------------------------------------------
  const fileErrors = ir.diagnostics.filter((d) => d.severity === "error");
  const declarations = new Map(parsed.functions.map((decl) => [decl.name, decl]));
  const byName = new Map(ir.functions.map((fn) => [fn.name, fn]));
  const rejected = new Map<string, Diagnostic[]>();
  for (const fn of ir.functions) {
    const decl = declarations.get(fn.name);
    const own = fileErrors.filter((d) => functionOwns(fn, decl, d));
    if (own.length > 0) rejected.set(fn.name, [...own]);
  }

  // --- a rejected function's spec may still be used by callers (lenient mode) -------------
  for (const name of rejected.keys()) {
    uncertified.add(name);
    const fn = byName.get(name);
    if (strict || fn === undefined) continue;
    const added = K.addDecl(env, {
      kind: "external",
      name,
      type: fn.signature.type,
      source: { file: path, hash },
    });
    if (added.ok) env = added.value;
  }

  // --- elaboration, callees before callers ------------------------------------------------
  const order = elaborationOrder(ir.functions, rejected);
  for (const fn of order.functions) {
    const own = rejected.get(fn.name);
    if (own !== undefined) {
      verdicts.push({
        name: fn.name,
        exported: fn.exported,
        span: fn.span,
        status: "rejected",
        certified: false,
        obligations: [],
        dependsOnUncertified: [],
      });
      plan.push(...planFor(fn, declarations.get(fn.name), "rejected"));
      continue;
    }
    const outcome = elaborateFunction(env, fn, {
      timeoutMs: options.timeoutMs,
      functions: byName,
      uncertified,
      sourceHash: hash,
      admitUncertified: !strict,
      solver,
    });
    env = outcome.env;
    if (outcome.declarationError !== undefined) diagnostics.push(outcome.declarationError);
    diagnostics.push(...outcome.result.diagnostics);
    if (!outcome.result.certified) uncertified.add(fn.name);
    verdicts.push({
      name: fn.name,
      exported: fn.exported,
      span: fn.span,
      status: outcome.result.status,
      certified: outcome.result.certified,
      obligations: outcome.result.obligations,
      dependsOnUncertified: outcome.result.dependsOnUncertified,
    });
    plan.push(
      ...planFor(
        fn,
        declarations.get(fn.name),
        outcome.result.certified ? "certified" : outcome.result.status,
        new Map(outcome.result.obligations.map((o) => [o.siteId, o])),
      ),
    );
  }
  for (const fn of order.unreachable) {
    diagnostics.push({
      kind: "internal",
      severity: "error",
      span: fn.nameSpan,
      message:
        `\`${fn.name}\` is part of a cycle of local calls (mutual recursion), which is not ` +
        `implemented yet (milestone 7 part B)`,
    });
    verdicts.push({
      name: fn.name,
      exported: fn.exported,
      span: fn.span,
      status: "failed",
      certified: false,
      obligations: [],
      dependsOnUncertified: [],
    });
    plan.push(...planFor(fn, declarations.get(fn.name), "failed"));
  }

  const axioms = K.axiomsUsed(env);
  const sorted = sortDiagnostics(diagnostics);
  const ok = resultOk(verdicts, sorted, axioms, strict);
  return {
    path,
    strict,
    ok,
    functions: verdicts,
    diagnostics: sorted,
    plan,
    externals,
    axioms,
    env,
  };
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function resultOk(
  verdicts: readonly FunctionVerdict[],
  diagnostics: readonly Diagnostic[],
  axioms: readonly string[],
  strict: boolean,
): boolean {
  if (axioms.length > 0) return false;
  if (hasErrors(diagnostics)) return false;
  for (const verdict of verdicts) {
    if (verdict.status === "certified") {
      if (strict && verdict.dependsOnUncertified.length > 0) return false;
      continue;
    }
    if (verdict.status === "smt-only") {
      if (strict) return false;
      continue;
    }
    return false;
  }
  return true;
}

/** Every distinct imported spec used by a function of this file, in first-use order. */
function allImports(functions: readonly FunctionIR[]): ImportedSpec[] {
  const seen = new Set<string>();
  const out: ImportedSpec[] = [];
  for (const fn of functions) {
    for (const spec of fn.imports) {
      if (seen.has(spec.name)) continue;
      seen.add(spec.name);
      out.push(spec);
    }
  }
  return out;
}

/** A location for a diagnostic about an imported declaration: the file it came from. */
function importSpan(spec: ImportedSpec): Span {
  return { file: spec.file, line: 1, col: 1, offset: 0 };
}

/** True when a diagnostic belongs to this function (its declaration or its JSDoc). */
function functionOwns(fn: FunctionIR, decl: FnDecl | undefined, diagnostic: Diagnostic): boolean {
  if (spanContains(fn.span, diagnostic.span)) return true;
  if (spanContains(fn.nameSpan, diagnostic.span)) return true;
  if (decl?.jsdoc != null && spanContains(decl.jsdoc.span, diagnostic.span)) return true;
  return false;
}

/** Part B: a loop or a recursive function (reported, not elaborated, in part A). */
function isPartB(fn: FunctionIR): boolean {
  return fn.recursive || fn.loops.length > 0;
}

/**
 * The elaboration order: every local callee before its caller.  Functions that are part B
 * (a loop or recursion) keep their source position and are elaborated by the dispatcher
 * below, which reports the missing feature; functions in a cycle of local calls are
 * unreachable and reported as such.
 */
function elaborationOrder(
  functions: readonly FunctionIR[],
  rejected: ReadonlyMap<string, Diagnostic[]>,
): { functions: FunctionIR[]; unreachable: FunctionIR[] } {
  const byName = new Map(functions.map((fn) => [fn.name, fn]));
  const done = new Set<string>([...rejected.keys()]);
  const pending = functions.filter((fn) => !rejected.has(fn.name) && !isPartB(fn));
  const other = functions.filter((fn) => rejected.has(fn.name) !== true && isPartB(fn));
  const out: FunctionIR[] = [];
  let progress = true;
  while (progress) {
    progress = false;
    for (const fn of pending) {
      if (out.includes(fn)) continue;
      const waiting = localCallees(fn, byName).some((name) => {
        const callee = byName.get(name);
        return callee !== undefined && !isPartB(callee) && !done.has(name) && !rejected.has(name);
      });
      if (waiting) continue;
      out.push(fn);
      done.add(fn.name);
      progress = true;
    }
  }
  const unreachable = pending.filter((fn) => !out.includes(fn));
  const rejectedFunctions = functions.filter((fn) => rejected.has(fn.name));
  return {
    // Rejected functions are reported by the verdict loop; the rest is elaborated.
    functions: [...out, ...other, ...rejectedFunctions].sort((a, b) => a.span.offset - b.span.offset),
    unreachable,
  };
}

/** Names of local functions a function calls (recursion included). */
function localCallees(fn: FunctionIR, byName: ReadonlyMap<string, FunctionIR>): string[] {
  const out = new Set<string>();
  const visitExpr = (e: import("./extract/fragment").ExprIR): void => {
    if (e.kind === "call" && e.callee !== undefined) {
      if (e.callee.kind === "local" && byName.has(e.callee.name)) out.add(e.callee.name);
    }
    for (const arg of e.args) visitExpr(arg);
    if (e.vecLength !== undefined) visitExpr(e.vecLength);
    if (e.cond !== undefined) {
      visitExpr(e.cond.expr);
      if (e.cond.thenExpr !== undefined) visitExpr(e.cond.thenExpr);
      if (e.cond.elseExpr !== undefined) visitExpr(e.cond.elseExpr);
    }
  };
  const visitStmts = (stmts: readonly import("./extract/fragment").StmtIR[]): void => {
    for (const stmt of stmts) {
      switch (stmt.kind) {
        case "local":
          visitExpr(stmt.value);
          break;
        case "expr":
          visitExpr(stmt.expr);
          break;
        case "return":
          visitExpr(stmt.value);
          break;
        case "if":
          visitExpr(stmt.cond.expr);
          visitStmts(stmt.then);
          visitStmts(stmt.otherwise);
          break;
        case "switch":
          for (const c of stmt.cases) visitStmts(c.body);
          break;
        case "loop":
          visitStmts(stmt.loop.body);
          visitStmts(stmt.loop.rest);
          break;
        default:
          break;
      }
    }
  };
  visitStmts(fn.body);
  return [...out];
}

/**
 * The injection plan for one function: boundary guards, entry precondition checks, return
 * postcondition checks and one record per internal obligation site.  Milestone 8 owns the
 * actual injection; this is the data it needs.
 */
function planFor(
  fn: FunctionIR,
  decl: FnDecl | undefined,
  status: Verdict,
  obligations?: ReadonlyMap<number, ObligationOutcome>,
): InjectionRecord[] {
  const out: InjectionRecord[] = [];
  const certified = status === "certified";
  const paramText = new Map<string, string>();
  for (const param of decl?.params ?? []) paramText.set(param.name, param.typeText ?? "number");
  if (fn.exported) {
    for (const param of fn.params) {
      out.push({
        function: fn.name,
        exported: fn.exported,
        kind: "guard",
        span: param.span,
        specText: paramText.get(param.name) ?? param.type.kind,
        certified,
        isPrecondition: false,
        isBoundaryGuard: true,
        param: param.name,
      });
    }
  }
  const preTags = decl?.jsdoc == null ? [] : tagsNamed(decl.jsdoc, "pre");
  fn.signature.preconditions.forEach((pre, index) => {
    out.push({
      function: fn.name,
      exported: fn.exported,
      kind: "pre",
      span: preTags[index]?.span ?? fn.span,
      specText: preTags[index]?.text ?? pre.text ?? "",
      certified,
      isPrecondition: true,
      isBoundaryGuard: false,
    });
  });
  const postStatuses = fn.sites.filter((site) => site.kind === "post");
  const postsCertified =
    postStatuses.length > 0 && postStatuses.every((site) => obligations?.get(site.id)?.status === "certified");
  const postTags = decl?.jsdoc == null ? [] : tagsNamed(decl.jsdoc, "post");
  fn.signature.result.posts.forEach((post, index) => {
    out.push({
      function: fn.name,
      exported: fn.exported,
      kind: "post",
      span: postTags[index]?.span ?? fn.span,
      specText: postTags[index]?.text ?? post.text ?? "",
      certified: postsCertified,
      isPrecondition: false,
      isBoundaryGuard: false,
    });
  });
  for (const site of fn.sites) {
    if (site.kind === "post") continue;
    const outcome = obligations?.get(site.id);
    out.push({
      function: fn.name,
      exported: fn.exported,
      kind: site.kind,
      span: site.span,
      specText: site.text,
      certified: outcome?.status === "certified",
      isPrecondition: site.kind === "pre-call",
      isBoundaryGuard: false,
      siteId: site.id,
    });
  }
  return out;
}

/** Whether an imported function is certified in its own file, when the caller asked. */
function importCertified(spec: ImportedSpec, options: VerifyOptions): boolean | "unknown" {
  try {
    let source: string | undefined;
    if (options.readFile !== undefined) {
      source = options.readFile(spec.file);
    } else {
      const loaded = (options.resolver ?? new SpecResolver()).load(spec.file);
      if (loaded.ok) source = loaded.file.source;
    }
    if (source === undefined) return "unknown";
    const result = verify(spec.file, source, {
      strict: options.strict === true,
      timeoutMs: options.timeoutMs,
      resolver: options.resolver,
      readFile: options.readFile,
      verifyImports: false,
      solver: options.solver,
    });
    const verdict = result.functions.find((fn) => fn.name === spec.name);
    return verdict === undefined ? "unknown" : verdict.certified;
  } catch {
    return "unknown";
  }
}
