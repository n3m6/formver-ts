/**
 * SSA: local `let` variables and loops become local recursive functions built with `fixWf`
 * (specification 6.3).
 *
 * A loop is lowered to a local function over a tuple of the loop-carried variables:
 *
 * ```text
 * loop(s) = if cond(s) then body(s, continue = loop(s'), return = ret) else rest(s)
 * ```
 *
 * Its precondition is the `@invariant` (the body assumes it; every back edge owes it again)
 * and its measure is `@decreases` (every back edge owes `Le 0 (m s')` and `Lt (m s') (m s)`).
 * Early `return`s inside the loop are returns from the loop function, which computes *the
 * rest of the function*: the statements after the loop become the `else` branch.
 *
 * The kernel side milestone 7 builds from a `LoopIR`:
 *
 * ```text
 * A    = Sigma (v0 : T0). Sigma (v1 : T1). … Unit      -- the carried-state tuple
 * B    = fun (_ : A) => Invariant s -> Result
 * m    = fun (s : A) => <@decreases>
 * step = fun (s : A) (px : Le 0 (m s)) (ih) (hinv : Invariant s) => if cond then body else rest
 * loop = fixWf A B m step s0 p0 hinv0 : Result
 * ```
 *
 * `fixWf` is opaque, so this recurses without unfolding; the recursive step is an application
 * of `ih`, which is what a `continue` statement records (the new state plus the two measure
 * obligations and the invariant-preservation obligation).
 *
 * The statement walker (`LoopHost.walk`) lives in `fragment.ts`; it threads the current value
 * of every carried variable, creates a fresh binder for each assignment (`x = e;` rebinds `x`
 * for the rest of that path) and duplicates the continuation into the branches of an `if`, so
 * no phi nodes are needed.
 */
import * as K from "../kernel/index";
import type { Mk, Term } from "../kernel/index";
import type { Span } from "../diagnostics";
import type * as A from "../syntax/ast";
import { tagsNamed, type JSDocTag } from "../syntax/jsdoc";
import { shiftTerm } from "./prelude";
import type {
  Binder,
  BinderRole,
  CondIR,
  Ctx,
  ExprIR,
  FactOrigin,
  Ids,
  LoopIR,
  LoopVarIR,
  ObligationKind,
  ObligationSite,
  Slot,
  StmtIR,
  TypeIR,
} from "./fragment";

/** One name in scope inside a loop body: where its current value lives. */
export interface EnvVar {
  readonly name: string;
  readonly slot: Slot;
  readonly type: TypeIR;
  readonly mutable: boolean;
  /** True for a function parameter, which may never be assigned. */
  readonly param: boolean;
  /** For a vector-typed variable: the expression denoting its length. */
  readonly lengthExpr?: ExprIR;
  readonly span: Span;
}

/** The value environment the statement walker threads through a block. */
export interface FnEnv {
  readonly vars: ReadonlyMap<string, EnvVar>;
}

/** The IR of everything after a statement list, in the scope that list ends in. */
export type Continuation = (ctx: Ctx, env: FnEnv) => StmtIR[];

export function envEmpty(): FnEnv {
  return { vars: new Map() };
}

export function envWith(env: FnEnv, variable: EnvVar): FnEnv {
  const vars = new Map(env.vars);
  vars.set(variable.name, variable);
  return { vars };
}

export function envLookup(env: FnEnv, name: string): EnvVar | undefined {
  return env.vars.get(name);
}

/** What `ssa.ts` needs from the fragment checker (`fragment.ts` implements it). */
export interface LoopHost {
  readonly ids: Ids;
  /** Add a binder to a context. */
  bindBinder(
    ctx: Ctx,
    name: string,
    type: Term,
    role: BinderRole,
    surface?: string,
    span?: Span,
  ): { ctx: Ctx; binder: Binder };
  /** Add an assumed proposition to a context. */
  addFact(ctx: Ctx, prop: ExprIR, origin: FactOrigin, binder?: Binder): Ctx;
  /** Parse a spec tag's expression text (the spec parser lives in `fragment.ts`). */
  parseTag(tag: JSDocTag): A.Expr | null;
  /** Check a boolean expression. */
  condition(ast: A.Expr, ctx: Ctx, env: FnEnv, spec?: boolean): CondIR | null;
  /** Check a value expression; `spec` suppresses body obligation sites. */
  expression(ast: A.Expr, ctx: Ctx, env: FnEnv, spec?: boolean): ExprIR | null;
  /** Walk a statement list to tail form; `k` produces the IR where the list falls through. */
  walk(
    stmts: readonly A.Stmt[],
    ctx: Ctx,
    env: FnEnv,
    k: Continuation,
    loop: LoopIR | null,
  ): StmtIR[];
  /** Report a located `fragment` error. */
  report(span: Span, message: string): void;
  /** `p1 && p2 && …`, binding each left operand as a hypothesis for the right one. */
  conjoin(parts: readonly ExprIR[], ctx: Ctx, env: FnEnv, span: Span): ExprIR;
  /** Register an obligation site. */
  site(kind: ObligationKind, span: Span, ctx: Ctx, goal: ExprIR, resultValue?: ExprIR): ObligationSite;
  /** A reference expression to a slot. */
  ref(slot: Slot, type: TypeIR, span: Span): ExprIR;
  /** The kernel type of a value of `type`, as a scope-aware builder. */
  typeMk(type: TypeIR): Mk;
  /** The `Mk` scope for a context, for building terms under fresh binders. */
  scope(ctx: Ctx): K.Scope;
  /** The kernel term of an expression, in a context. */
  term(ctx: Ctx, expr: ExprIR): Term;
  /** `Le a b`, `Lt a b` and `InRange a` as propositions, plus the trivial `Unit`. */
  le(a: ExprIR, b: ExprIR, span: Span): ExprIR;
  lt(a: ExprIR, b: ExprIR, span: Span): ExprIR;
  inRange(a: ExprIR, span: Span): ExprIR;
  trueExpr(span: Span): ExprIR;
  intExpr(value: bigint, span: Span): ExprIR;
}

export interface LoopRequest {
  readonly ast: A.WhileStmt | A.ForStmt;
  /** The context and environment at the loop, before the state tuple is introduced. */
  readonly ctx: Ctx;
  readonly env: FnEnv;
  /** The statements after the loop in the enclosing block. */
  readonly rest: readonly A.Stmt[];
  /** The IR of everything after the enclosing block. */
  readonly k: Continuation;
  /** The function's result type, in the enclosing context. */
  readonly resultType: Term;
  readonly span: Span;
}

// ---------------------------------------------------------------------------
// AST helpers
// ---------------------------------------------------------------------------

export function isLoop(stmt: A.Stmt): stmt is A.WhileStmt | A.ForStmt {
  return stmt.kind === "While" || stmt.kind === "For";
}

/** True when `node` assigns to `name` anywhere (used to decide what a loop carries). */
export function assignsTo(node: unknown, name: string): boolean {
  if (node === null || node === undefined || typeof node !== "object") return false;
  if (Array.isArray(node)) return node.some((item) => assignsTo(item, name));
  const record = node as Record<string, unknown>;
  const kind = record["kind"];
  if (kind === "Assign") {
    const target = record["target"] as A.Expr | undefined;
    if (target !== undefined && target.kind === "Ident" && target.name === name) return true;
  }
  if (kind === "Update") {
    const operand = record["operand"] as A.Expr | undefined;
    if (operand !== undefined && operand.kind === "Ident" && operand.name === name) return true;
  }
  return Object.values(record).some((value) => assignsTo(value, name));
}

/** `x++`, `x--`, `x += e` and `x -= e` as an `x = x + e` assignment AST node. */
export function desugarUpdate(update: A.Expr): A.Expr {
  if (update.kind === "Update" && update.operand.kind === "Ident") {
    const one: A.Lit = { kind: "Lit", lit: "int", raw: "1", value: 1n, span: update.span };
    const combined: A.BinaryExpr = {
      kind: "Binary",
      op: update.op === "++" ? "+" : "-",
      left: update.operand,
      right: one,
      span: update.span,
    };
    return { kind: "Assign", op: "=", target: update.operand, value: combined, span: update.span };
  }
  if (update.kind === "Assign" && (update.op === "+=" || update.op === "-=")) {
    const combined: A.BinaryExpr = {
      kind: "Binary",
      op: update.op === "+=" ? "+" : "-",
      left: update.target,
      right: update.value,
      span: update.span,
    };
    return { kind: "Assign", op: "=", target: update.target, value: combined, span: update.span };
  }
  return update;
}

/** The statement list a loop body runs: the body, plus a `for` loop's update. */
export function loopBodyStatements(ast: A.WhileStmt | A.ForStmt): readonly A.Stmt[] {
  if (ast.kind === "While") return [ast.body];
  const body: A.Stmt[] = [ast.body];
  if (ast.update !== null) {
    body.push({ kind: "ExprStmt", expr: desugarUpdate(ast.update), span: ast.update.span });
  }
  return body;
}

// ---------------------------------------------------------------------------
// The lowering
// ---------------------------------------------------------------------------

interface Carried {
  readonly name: string;
  readonly path: readonly number[];
  readonly type: TypeIR;
  readonly initial: ExprIR;
  readonly lengthExpr?: ExprIR;
  readonly span: Span;
}

/**
 * Lower one `while`/`for` statement.  Returns `null` only when the loop cannot be lowered at
 * all (a bad condition); every other problem is reported and the loop is still lowered with a
 * fallback `Unit` invariant or `0` measure, so the rest of the function is still checked.
 */
export function lowerLoop(host: LoopHost, request: LoopRequest): LoopIR | null {
  const { ast, ctx, env, rest, k, resultType, span } = request;

  const block = ast.jsdoc;
  const invariants = block === null ? [] : tagsNamed(block, "invariant");
  const decreases = block === null ? [] : tagsNamed(block, "decreases");
  if (block === null || invariants.length === 0) {
    host.report(
      block === null ? span : block.span,
      "a loop in a verified function needs a JSDoc block with `@invariant` and `@decreases`",
    );
  }
  if (decreases.length === 0) {
    host.report(
      block === null ? span : block.span,
      "a loop in a verified function needs a `@decreases` tag",
    );
  } else if (decreases.length > 1) {
    host.report(decreases[1]!.span, "a loop may have only one `@decreases` tag");
  }

  // ---- the carried variables -------------------------------------------------
  const bodyStmts = loopBodyStatements(ast);
  const mutated = new Set<string>();
  for (const variable of env.vars.values()) {
    if (!variable.mutable) continue;
    if (bodyStmts.some((stmt) => assignsTo(stmt, variable.name))) mutated.add(variable.name);
  }
  const carried: Carried[] = [];
  for (const name of mutated) {
    const variable = env.vars.get(name)!;
    carried.push({
      name,
      path: [],
      type: variable.type,
      initial: host.ref(variable.slot, variable.type, variable.span),
      lengthExpr: variable.lengthExpr,
      span: variable.span,
    });
  }
  // A `for (let i = e; c; update)` declares its own carried variable; `update` always
  // assigns it, so it is carried unconditionally.
  if (ast.kind === "For" && ast.init !== null && ast.init.kind === "VarDecl") {
    for (const declaration of ast.init.declarations) {
      if (declaration.init === undefined) continue;
      if (carried.some((c) => c.name === declaration.name)) continue;
      const value = host.expression(declaration.init, ctx, env);
      if (value === null) continue;
      carried.push({
        name: declaration.name,
        path: [],
        type: { kind: "int", span: declaration.span },
        initial: value,
        span: declaration.span,
      });
    }
  }

  // Paths: component `i` is `fst` after `snd` repeated `i` times (the tuple ends in `Unit`).
  const withPaths: Carried[] = carried.map((c, index) => ({ ...c, path: [...Array(index).fill(1), 0] }));

  // ---- the state tuple and the loop function's scope -------------------------
  const stateType = stateTypeTerm(host, ctx, withPaths);
  const stateBind = host.bindBinder(ctx, "s", stateType, "loop-state", undefined, span);
  const stateCtx = stateBind.ctx;
  const stateVar = K.varTerm(0);

  const measureTag = decreases[0];
  const measureEntry = checkIntTag(host, measureTag, stateCtx, entryEnv(host, env, stateBind.binder, withPaths), span);
  const invariantEntry =
    invariants.length === 0
      ? host.trueExpr(span)
      : conjoinTags(host, invariants, stateCtx, entryEnv(host, env, stateBind.binder, withPaths), span);
  const invariantTerm = host.term(stateCtx, invariantEntry);
  const measureFn: Term = K.lam(
    "s",
    stateType,
    measureEntry === null ? K.intLit(0n) : host.term(stateCtx, measureEntry),
  );
  const invariantFn: Term = K.lam("s", stateType, invariantTerm);

  // `px : Le 0 (m s)`, then `hinv : Invariant s`; both live under the state binder, so the
  // previously built terms are shifted by one for each new binder.
  const pxType = K.Le(K.intLit(0n), K.app(shiftTerm(measureFn, 1), stateVar));
  const pxBind = host.bindBinder(stateCtx, "px", pxType, "loop-measure-nonneg");
  const measureFact = host.addFact(
    pxBind.ctx,
    host.le(host.intExpr(0n, span), measureEntry ?? host.intExpr(0n, span), span),
    "measure",
    pxBind.binder,
  );
  const hinvBind = host.bindBinder(measureFact, "hinv", shiftTerm(invariantTerm, 1), "invariant");
  const bodyCtx = host.addFact(hinvBind.ctx, invariantEntry, "invariant", hinvBind.binder);

  const resultMotive: Term = K.lam("_", stateType, K.pi("hinv", invariantTerm, shiftTerm(resultType, 2)));

  const bodyEnv = entryEnv(host, env, stateBind.binder, withPaths);
  const test = host.condition(loopTest(ast), bodyCtx, bodyEnv);
  if (test === null) return null;

  // ---- the loop node (its body and rest are filled in after the walks) --------
  const loopId = host.ids.fresh();
  const loop: LoopIR = {
    id: loopId,
    name: `loop${loopId}`,
    span,
    stateType,
    state: stateBind.binder,
    carried: withPaths.map(loopVar),
    invariant: invariantEntry,
    invariantType: invariantFn,
    measure: measureEntry ?? host.intExpr(0n, span),
    measureType: measureFn,
    invariantBinder: hinvBind.binder,
    resultMotive,
    resultType,
    test,
    body: [],
    rest: [],
    initSites: [],
  };

  // ---- the back edge ---------------------------------------------------------
  const backEdge: Continuation = (endCtx, endEnv) => {
    const values = withPaths.map((variable) => {
      const current = endEnv.vars.get(variable.name);
      const slot: Slot =
        current === undefined
          ? { kind: "state", state: stateBind.binder, path: variable.path, name: variable.name }
          : current.slot;
      const type = current === undefined ? variable.type : current.type;
      return { variable: loopVar(variable), value: host.ref(slot, type, span) };
    });
    const invariantNew =
      invariants.length === 0 ? host.trueExpr(span) : conjoinTags(host, invariants, endCtx, endEnv, span);
    const measureNew = checkIntTag(host, measureTag, endCtx, endEnv, span) ?? host.intExpr(0n, span);
    const sites: ObligationSite[] = [
      host.site("invariant-preserve", span, endCtx, invariantNew),
      host.site("measure-nonneg", span, endCtx, host.le(host.intExpr(0n, span), measureNew, span)),
      host.site("measure-decrease", span, endCtx, host.lt(measureNew, measureEntry ?? host.intExpr(0n, span), span)),
    ];
    const node: StmtIR = { kind: "continue", loop, values, sites, span };
    return [node];
  };

  loop.body = host.walk(bodyStmts, bodyCtx, bodyEnv, backEdge, loop);
  // The statements after the loop run *outside* the loop, so an assignment there is rejected
  // (section 4.2 allows reassignment only inside a loop).
  loop.rest = host.walk(rest, bodyCtx, bodyEnv, k, null);

  // ---- the init obligations, in the enclosing context ------------------------
  const invariantInit =
    invariants.length === 0 ? host.trueExpr(span) : conjoinTags(host, invariants, ctx, env, span);
  const measureInit = checkIntTag(host, measureTag, ctx, env, span) ?? host.intExpr(0n, span);
  loop.initSites = [
    host.site("invariant-init", span, ctx, invariantInit),
    host.site("measure-nonneg", span, ctx, host.le(host.intExpr(0n, span), measureInit, span)),
  ];

  return loop;
}

/** The body environment: every carried variable is a component of the state tuple. */
function entryEnv(host: LoopHost, env: FnEnv, state: Binder, carried: readonly Carried[]): FnEnv {
  void host;
  const vars = new Map(env.vars);
  for (const variable of carried) {
    vars.set(variable.name, {
      name: variable.name,
      slot: { kind: "state", state, path: variable.path, name: variable.name },
      type: variable.type,
      mutable: true,
      param: false,
      lengthExpr: variable.lengthExpr,
      span: variable.span,
    });
  }
  return { vars };
}

function loopVar(variable: Carried): LoopVarIR {
  return {
    name: variable.name,
    path: variable.path,
    type: variable.type,
    initial: variable.initial,
  };
}

/** The carried-state tuple: `Sigma (v0 : T0). Sigma (v1 : T1). … Unit`. */
function stateTypeTerm(host: LoopHost, ctx: Ctx, carried: readonly Carried[]): Term {
  let out: Mk = () => K.Unit;
  for (let i = carried.length - 1; i >= 0; i -= 1) {
    const inner = out;
    const name = carried[i]!.name;
    const type = host.typeMk(carried[i]!.type);
    out = (scope) => K.sigma(name, type(scope), inner(scope.bind(name)));
  }
  return out(host.scope(ctx));
}

function checkIntTag(
  host: LoopHost,
  tag: JSDocTag | undefined,
  ctx: Ctx,
  env: FnEnv,
  span: Span,
): ExprIR | null {
  if (tag === undefined) return null;
  const ast = host.parseTag(tag);
  if (ast === null) return null;
  const checked = host.expression(ast, ctx, env, true);
  if (checked === null) return null;
  if (checked.type.kind !== "int") {
    host.report(tag.textSpan, "`@decreases` must be a non-negative integer expression");
    return null;
  }
  return checked;
}

function conjoinTags(
  host: LoopHost,
  tags: readonly JSDocTag[],
  ctx: Ctx,
  env: FnEnv,
  span: Span,
): ExprIR {
  const parts: ExprIR[] = [];
  for (const tag of tags) {
    const ast = host.parseTag(tag);
    if (ast === null) continue;
    const checked = host.expression(ast, ctx, env, true);
    if (checked === null || checked.kind === "true") continue;
    if (checked.type.kind !== "boolean") {
      host.report(tag.textSpan, "`@invariant` must be a boolean expression");
      continue;
    }
    parts.push(checked);
  }
  if (parts.length === 0) return host.trueExpr(span);
  return host.conjoin(parts, ctx, env, span);
}

function loopTest(ast: A.WhileStmt | A.ForStmt): A.Expr {
  if (ast.kind === "While") return ast.test;
  if (ast.test !== null) return ast.test;
  return { kind: "Lit", lit: "boolean", raw: "true", value: true, span: ast.span };
}
