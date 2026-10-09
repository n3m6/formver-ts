/**
 * Validity checks, counterexamples, Farkas multiplier search and proof-term construction
 * (specification 6.4).
 *
 * `certify(env, obligation)` is the untrusted bridge between Z3 and the trusted kernel:
 *
 *   1. **Proof search.** The goal is decomposed structurally — conjunctions component-wise,
 *      `===` as two `Le` goals combined with `intEq`, `||` as `inl`/`inr` or an `ifLe`
 *      split, `!==` and `||` *hypotheses* as case splits — until every leaf is a `Le` goal.
 *      Each leaf asks Z3 for a Farkas certificate over the *tightened* rows (`linear.ts`)
 *      and builds `byContra a b (k => Farkas [hyps…, k] [λ…])`. A leaf whose hypotheses are
 *      already contradictory becomes `absurd goal (Farkas [hyps…] [λ…])`.
 *   2. **Validity.** If no proof was found, the original hypotheses and the negated goal go
 *      to Z3 in one query: `unsat` means the obligation is valid but had no certificate
 *      (**smt-only**), `sat` means it is invalid (a model is fetched and turned into a
 *      counterexample), and `unknown`/an error means not proven.
 *
 * Two invariants make the multipliers line up with the kernel:
 *
 *   - rows, and the atoms they mention, are computed with `linear.ts` — a deliberate copy
 *     of the kernel's arithmetic — from values evaluated in the obligation's ambient
 *     context with `values[level] = Var level`, so atom keys are exactly the keys the
 *     kernel will compute;
 *   - the hypothesis list handed to `Farkas` is the same list, in the same order, that the
 *     multipliers index.
 *
 * The proof is checked against the kernel before it is reported, whenever the obligation
 * carries its ambient context (then a kernel typing context can be rebuilt). A result with
 * `status: "certified"` therefore always has a `proof` the kernel accepts, and `certified`
 * is never claimed for an obligation that only Z3 proved.
 */
import * as K from "../kernel/index";
import { innermostProofs, obligationDepth, type Obligation } from "./obligations";
import * as L from "./linear";
import * as S from "./smtlib";
import * as Z from "./z3";

export type CertifyStatus = "certified" | "smt-only" | "failed";

export interface CertifyResult {
  /** `certified`: a kernel-acceptable proof. `smt-only`: Z3 proved it, no certificate. */
  readonly status: CertifyStatus;
  /** The proof of `proofType`, when `status` is `certified`. */
  readonly proof?: K.Term;
  /** What `proof` proves: the obligation's goal. */
  readonly proofType?: K.Term;
  /** The multipliers of the first certificate that was found, row order as `hypotheses`. */
  readonly multipliers?: bigint[];
  /** A model that violates the obligation, over the user's atom names. */
  readonly counterexample?: Record<string, string>;
  /** Case-split path that produced this result (the split hypotheses, outermost first). */
  readonly path?: string[];
  /** Why the obligation was not certified. Never empty for `failed`/`smt-only`. */
  readonly reason?: string;
}

export interface CertifyOptions {
  /** Per-query Z3 timeout; defaults to `z3.DEFAULT_TIMEOUT_MS`. */
  readonly timeoutMs?: number;
}

/** How many `ifLe` candidates a disjunction goal tries before giving up. */
const MAX_SPLIT_CANDIDATES = 6;

/** Set `DV_VC_DEBUG=1` to trace the proof search on stderr while developing. */
const DEBUG = process.env.DV_VC_DEBUG === "1";
function debug(...parts: unknown[]): void {
  if (DEBUG) console.error("[vc]", ...parts);
}

interface Ambience {
  readonly env: K.Env;
  readonly depth: number;
  readonly atoms: S.AtomTable;
  readonly timeoutMs: number;
  readonly atomNames: Readonly<Record<string, string>>;
  /** The kernel typing context, when the obligation carried its ambient binder types. */
  readonly ctx: K.Ctx | undefined;
}

interface Hypothesis {
  readonly proposition: L.Proposition;
  /** The proof term, in the current scope (ambient binders plus `extra` splits). */
  readonly proof: K.Term;
  readonly text: string;
}

interface Case {
  readonly hyps: readonly Hypothesis[];
  readonly goal: L.Proposition;
  /** How many binders the case splits have introduced. */
  readonly extra: number;
  readonly path: readonly string[];
}

type ProofOutcome =
  | { readonly ok: true; readonly proof: K.Term; readonly multipliers?: bigint[]; readonly path: readonly string[] }
  | { readonly ok: false; readonly reason: string; readonly path: readonly string[] };

type ValidityOutcome =
  | { readonly kind: "valid" }
  | { readonly kind: "invalid"; readonly counterexample: Record<string, string> }
  | { readonly kind: "unknown"; readonly reason: string };

/** Certify one obligation. Never throws: an internal error becomes a `failed` result. */
export function certify(env: K.Env, obligation: Obligation, opts: CertifyOptions = {}): CertifyResult {
  try {
    return certifyObligation(env, obligation, opts);
  } catch (cause) {
    const message = cause instanceof Error ? cause.message : String(cause);
    return { status: "failed", reason: `internal error while certifying ${obligation.id}: ${message}` };
  }
}

function certifyObligation(env: K.Env, obligation: Obligation, opts: CertifyOptions): CertifyResult {
  const depth = obligationDepth(obligation);
  const ctx = buildContext(env, obligation.context);
  const amb: Ambience = {
    env,
    depth,
    atoms: new S.AtomTable(env, depth),
    timeoutMs: Z.effectiveTimeout(opts.timeoutMs),
    atomNames: obligation.atomNames ?? {},
    ctx: obligation.context === undefined ? undefined : ctx,
  };

  // --- hypotheses: propositions (from the kernel's own view when possible) and proofs ---
  const hyps: Hypothesis[] = [];
  const hypPropositions: L.Proposition[] = [];
  for (let index = 0; index < obligation.hypotheses.length; index += 1) {
    const term = obligation.hypotheses[index]!;
    const proof = resolveProof(amb, obligation, index, term);
    if (proof === undefined) {
      return {
        status: "failed",
        reason:
          `obligation ${obligation.id} does not say where the proof of hypothesis ${index} lives: ` +
          `pass \`proofs\` (one term per hypothesis) or a \`context\` that binds it, or make the ` +
          `hypotheses the innermost binders of the context`,
      };
    }
    const proposition = propositionOfHypothesis(amb, term, proof);
    hyps.push({ proposition, proof, text: L.propositionText(proposition) });
    hypPropositions.push(proposition);
  }
  const goal = L.propositionOfTerm(env, depth, obligation.goal);
  const root: Case = { hyps, goal, extra: 0, path: [] };

  // --- phase 1: build a proof ---
  const outcome = prove(amb, root);
  debug("root goal " + L.propositionText(goal) + " -> " + (outcome.ok ? "proof " + K.formatTerm(outcome.proof) : "failed: " + outcome.reason));
  if (outcome.ok) {
    const checked = kernelCheck(amb, outcome.proof, goal, obligation);
    if (!checked.ok) {
      return { status: "failed", path: [...outcome.path], reason: checked.reason };
    }
    return {
      status: "certified",
      proof: outcome.proof,
      proofType: obligation.goal,
      ...(outcome.multipliers === undefined ? {} : { multipliers: outcome.multipliers }),
      path: [...outcome.path],
    };
  }

  // --- phase 2: is the obligation valid at all? ---
  const validity = checkValidity(amb, hypPropositions, goal);
  if (validity.kind === "invalid") {
    return {
      status: "failed",
      counterexample: validity.counterexample,
      path: [...outcome.path],
      reason: `the obligation does not hold (${outcome.reason})`,
    };
  }
  if (validity.kind === "valid") {
    return {
      status: "smt-only",
      path: [...outcome.path],
      reason: "Z3 proved the obligation but no Farkas certificate was found for its tightened rows",
    };
  }
  // Neither a proof nor a verdict: report why, once (the two reasons are often the same,
  // for example when Z3 itself is unavailable).
  const reasons = [validity.reason, outcome.reason].filter(
    (reason, index, all) => reason !== "" && all.indexOf(reason) === index,
  );
  return { status: "failed", path: [...outcome.path], reason: reasons.join("; ") };
}

// ---------------------------------------------------------------------------
// Ambient context, hypotheses
// ---------------------------------------------------------------------------

/**
 * The kernel typing context of the obligation's ambient binders. `types[level]` is the
 * type of the variable at that level, evaluated in the preceding variables — exactly how
 * `check.ts` builds its own context, and what makes atom levels (`Var level`) agree.
 */
function buildContext(env: K.Env, domains: readonly K.Term[] | undefined): K.Ctx {
  if (domains === undefined) return K.emptyCtx(env);
  const types: K.Value[] = [];
  // Every iteration hands `evalTerm` a *fresh* array: a `Pi`/`Sigma`/`Lam` value created
  // while evaluating a domain captures the environment array by reference, so appending to
  // the array in place would later change what a closure created here refers to — a
  // dependent domain (a `Vec` element guard, say) would then read the wrong variable.
  let values: K.Value[] = [];
  for (let level = 0; level < domains.length; level += 1) {
    types.push(K.evalTerm(env, domains[level]!, values));
    values = [...values, K.vvar(level)];
  }
  return { env, types, values };
}

/**
 * The proof term of hypothesis `index`: `proofs[index]` when given, else a context binder
 * whose type is convertible to the hypothesis proposition. With a context but no match the
 * obligation is rejected rather than guessed at; without a context, the documented
 * "innermost binders" fallback applies (and only then is it meaningful).
 */
function resolveProof(amb: Ambience, obligation: Obligation, index: number, term: K.Term): K.Term | undefined {
  const count = obligation.hypotheses.length;
  if (obligation.proofs !== undefined) {
    return obligation.proofs.length === count ? obligation.proofs[index] : undefined;
  }
  const ctx = amb.ctx;
  if (ctx !== undefined) {
    let value: K.Value | undefined;
    try {
      value = K.evalTerm(amb.env, term, ctx.values);
    } catch {
      value = undefined;
    }
    if (value !== undefined) {
      for (let level = 0; level < ctx.types.length; level += 1) {
        const domain = ctx.types[level]!;
        try {
          if (K.convValue(amb.env, amb.depth, domain, value)) return K.varTerm(amb.depth - 1 - level);
        } catch {
          // An ill-typed pair of values cannot be convertible; keep looking.
        }
      }
    }
    return undefined;
  }
  // The documented fallback: the hypotheses really are the innermost binders.
  return amb.depth >= count ? innermostProofs(count)[index] : undefined;
}

/**
 * A hypothesis's proposition. With an ambient context the kernel is asked for the type of
 * the proof term (that is exactly what `checkFarkas` will see); otherwise the proposition
 * term is evaluated directly.
 */
function propositionOfHypothesis(amb: Ambience, term: K.Term, proof: K.Term): L.Proposition {
  if (amb.ctx !== undefined) {
    try {
      const inferred = K.infer(amb.ctx, proof);
      if (inferred.ok) return L.propositionOfValue(amb.env, amb.depth, inferred.value);
    } catch {
      // Fall through to the syntactic proposition.
    }
  }
  return L.propositionOfTerm(amb.env, amb.depth, term);
}

/**
 * A new case in which hypothesis `index` has been *eliminated* — its proof is the scrutinee
 * of a `case`/`ifLe` — so the split cannot happen twice. One new hypothesis takes the
 * innermost binder, and every other hypothesis moves one binder deeper.
 */
function eliminateHypothesis(cs: Case, index: number, added: L.Proposition): Case {
  return {
    hyps: [
      ...cs.hyps
        .filter((_, at) => at !== index)
        .map((other) => ({ ...other, proof: L.shift(other.proof, 1) })),
      { proposition: added, proof: K.varTerm(0), text: L.propositionText(added) },
    ],
    goal: cs.goal,
    extra: cs.extra + 1,
    path: [...cs.path, L.propositionText(added)],
  };
}

/** A new case with one more hypothesis, bound as the innermost variable. */
function addHypothesis(cs: Case, proposition: L.Proposition, text: string): Case {
  return {
    hyps: [
      ...cs.hyps.map((hypothesis) => ({ ...hypothesis, proof: L.shift(hypothesis.proof, 1) })),
      { proposition, proof: K.varTerm(0), text },
    ],
    goal: cs.goal,
    extra: cs.extra + 1,
    path: [...cs.path, text],
  };
}

/** Every hypothesis as a row, with the proof term the kernel will see for it. */
function linearizeHyps(amb: Ambience, cs: Case): L.RowEntry[] {
  const entries: L.RowEntry[] = [];
  for (const hypothesis of cs.hyps) {
    entries.push(...L.linearize(amb.env, amb.depth, hypothesis.proposition, hypothesis.proof, cs.extra).entries);
  }
  return entries;
}

// ---------------------------------------------------------------------------
// Proof search
// ---------------------------------------------------------------------------

function prove(amb: Ambience, cs: Case): ProofOutcome {
  // A hypothesis that is a disjunction or a disequality has to be split before any leaf
  // can see the linear facts it hides (section 6.4).
  for (let index = 0; index < cs.hyps.length; index += 1) {
    const split = splitHypothesis(amb, cs, index);
    if (split !== undefined) return split;
  }
  switch (cs.goal.kind) {
    case "unit":
      return { ok: true, proof: K.tt, path: cs.path };
    case "and":
      return proveConjunction(amb, cs);
    case "eq":
      return proveEquality(amb, cs);
    case "le":
      return proveLe(amb, cs);
    case "empty":
      return proveEmpty(amb, cs);
    case "sum":
      return proveDisjunction(amb, cs);
    case "not":
      return proveNegation(amb, cs);
    case "other":
      return absurdFallback(amb, cs, `the goal ${L.propositionText(cs.goal)} is outside the fragment`);
  }
}

function proveConjunction(amb: Ambience, cs: Case): ProofOutcome {
  if (cs.goal.kind !== "and") return unreachable(cs);
  const first = prove(amb, { ...cs, goal: cs.goal.first });
  if (!first.ok) return absurdFallback(amb, cs, first.reason);
  const second = prove(amb, { ...cs, goal: cs.goal.second });
  if (!second.ok) return absurdFallback(amb, cs, second.reason);
  return {
    ok: true,
    proof: K.pair(L.shift(L.propositionTerm(cs.goal), cs.extra), first.proof, second.proof),
    multipliers: first.multipliers ?? second.multipliers,
    path: cs.path,
  };
}

function proveEquality(amb: Ambience, cs: Case): ProofOutcome {
  if (cs.goal.kind !== "eq") return unreachable(cs);
  const goal = cs.goal;
  if (goal.type.tag === "Prim" && goal.type.op === K.OP_INT) {
    const forward = prove(amb, { ...cs, goal: { kind: "le", lhs: goal.lhs, rhs: goal.rhs } });
    if (!forward.ok) return absurdFallback(amb, cs, forward.reason);
    const backward = prove(amb, { ...cs, goal: { kind: "le", lhs: goal.rhs, rhs: goal.lhs } });
    if (!backward.ok) return absurdFallback(amb, cs, backward.reason);
    return {
      ok: true,
      proof: K.IntEq(
        L.shift(goal.lhs, cs.extra),
        L.shift(goal.rhs, cs.extra),
        forward.proof,
        backward.proof,
      ),
      multipliers: forward.multipliers ?? backward.multipliers,
      path: cs.path,
    };
  }
  if (termsConvertible(amb, goal.lhs, goal.rhs)) {
    return {
      ok: true,
      proof: K.Refl(L.shift(goal.type, cs.extra), L.shift(goal.lhs, cs.extra)),
      path: cs.path,
    };
  }
  return absurdFallback(amb, cs, `the equality ${L.propositionText(goal)} is not an integer equality`);
}

function proveLe(amb: Ambience, cs: Case): ProofOutcome {
  if (cs.goal.kind !== "le") return unreachable(cs);
  const goal = cs.goal;
  const entries = linearizeHyps(amb, cs);
  // The `no` branch of `byContra a b` assumes `Lt b a`, i.e. `Le (b + 1) a`.
  const negatedForm = L.formOfDifference(amb.env, amb.depth, K.Add(goal.rhs, K.intLit(1n)), goal.lhs);
  const rows = [
    ...entries.map((entry) => L.tightenRow(entry.row)),
    L.tightenRow(L.rowOfForm(negatedForm)),
  ];
  const printed: S.PrintedRow[] = [
    ...entries.map((entry) => ({ row: L.tightenRow(entry.row), atoms: entry.atoms })),
    { row: L.tightenRow(L.rowOfForm(negatedForm)), atoms: negatedForm.atoms },
  ];
  const found = findCertificate(amb, rows, printed);
  debug("leaf " + L.propositionText(goal) + " -> " + (found.ok ? "certificate " + found.lambda.join(",") : "no certificate: " + found.error));
  if (!found.ok) return absurdFallback(amb, cs, found.error);
  const lhs = L.shift(goal.lhs, cs.extra);
  const rhs = L.shift(goal.rhs, cs.extra);
  return {
    ok: true,
    proof: K.ByContra(
      lhs,
      rhs,
      K.lam(
        "_k",
        K.Lt(rhs, lhs),
        K.Farkas([...entries.map((entry) => L.shift(entry.proof, 1)), K.varTerm(0)], found.lambda),
      ),
    ),
    multipliers: found.lambda,
    path: cs.path,
  };
}

function proveEmpty(amb: Ambience, cs: Case): ProofOutcome {
  const entries = linearizeHyps(amb, cs);
  if (entries.length === 0) {
    return { ok: false, reason: "the hypotheses are empty, so they cannot be contradictory", path: cs.path };
  }
  const rows = entries.map((entry) => L.tightenRow(entry.row));
  const printed: S.PrintedRow[] = entries.map((entry) => ({
    row: L.tightenRow(entry.row),
    atoms: entry.atoms,
  }));
  const found = findCertificate(amb, rows, printed);
  if (!found.ok) return { ok: false, reason: found.error, path: cs.path };
  return {
    ok: true,
    proof: K.Farkas(entries.map((entry) => entry.proof), found.lambda),
    multipliers: found.lambda,
    path: cs.path,
  };
}

function proveDisjunction(amb: Ambience, cs: Case): ProofOutcome {
  if (cs.goal.kind !== "sum") return unreachable(cs);
  const goal = cs.goal;
  const leftTerm = L.shift(L.propositionTerm(goal.left), cs.extra);
  const rightTerm = L.shift(L.propositionTerm(goal.right), cs.extra);
  const direct = prove(amb, { ...cs, goal: goal.left });
  if (direct.ok) {
    return {
      ok: true,
      proof: K.Inl(leftTerm, rightTerm, direct.proof),
      multipliers: direct.multipliers,
      path: cs.path,
    };
  }
  const directRight = prove(amb, { ...cs, goal: goal.right });
  if (directRight.ok) {
    return {
      ok: true,
      proof: K.Inr(leftTerm, rightTerm, directRight.proof),
      multipliers: directRight.multipliers,
      path: cs.path,
    };
  }
  const candidates = L.comparisonCandidates(goal).slice(0, MAX_SPLIT_CANDIDATES);
  for (const candidate of candidates) {
    const orders: readonly { readonly yesIsLeft: boolean }[] = [{ yesIsLeft: true }, { yesIsLeft: false }];
    for (const order of orders) {
      const comparison: L.Proposition = { kind: "le", lhs: candidate.lhs, rhs: candidate.rhs };
      const yesCase = addHypothesis(cs, comparison, L.propositionText(comparison));
      const yes = prove(amb, { ...yesCase, goal: order.yesIsLeft ? goal.left : goal.right });
      if (!yes.ok) continue;
      const negated: L.Proposition = {
        kind: "le",
        lhs: K.Add(candidate.rhs, K.intLit(1n)),
        rhs: candidate.lhs,
      };
      const noCase = addHypothesis(cs, negated, L.propositionText(negated));
      const no = prove(amb, { ...noCase, goal: order.yesIsLeft ? goal.right : goal.left });
      if (!no.ok) continue;
      const lhs = L.shift(candidate.lhs, cs.extra);
      const rhs = L.shift(candidate.rhs, cs.extra);
      // A branch of `ifLe` returns the motive (the disjunction), so each branch's proof of
      // its disjunct is injected into the `Sum` it belongs to.
      // The branch bodies sit under one more binder, so the type arguments of the
      // injection are lifted with them.
      const inject = (isLeft: boolean, proof: K.Term): K.Term =>
        isLeft
          ? K.Inl(L.shift(leftTerm, 1), L.shift(rightTerm, 1), proof)
          : K.Inr(L.shift(leftTerm, 1), L.shift(rightTerm, 1), proof);
      debug("disjunction split on " + L.propositionText(comparison));
      return {
        ok: true,
        proof: K.IfLe(
          0,
          L.shift(L.propositionTerm(goal), cs.extra),
          lhs,
          rhs,
          K.lam("_h", K.Le(lhs, rhs), inject(order.yesIsLeft, yes.proof)),
          K.lam("_h", K.Lt(rhs, lhs), inject(!order.yesIsLeft, no.proof)),
        ),
        multipliers: yes.multipliers ?? no.multipliers,
        path: cs.path,
      };
    }
  }
  return absurdFallback(amb, cs, `neither disjunct of ${L.propositionText(goal)} is provable, and no \`ifLe\` split works`);
}

/**
 * Split a hypothesis that is not linear:
 *
 *   - `A || B` is a `Sum`, eliminated with the kernel's dependent `case`;
 *   - `a !== b` is `Not (Eq Int a b)`; over the integers it is `a < b` or `b < a`, so an
 *     `ifLe a b` split covers it: the `yes` branch gets `a <= b` and derives `a < b` by
 *     contradicting the disequality with `intEq`, the `no` branch gets `b < a` directly.
 *
 * Returns `undefined` for a hypothesis that is already usable as a row.
 */
function splitHypothesis(amb: Ambience, cs: Case, index: number): ProofOutcome | undefined {
  const hypothesis = cs.hyps[index]!;
  const proposition = hypothesis.proposition;
  if (proposition.kind === "sum") {
    const sumTerm = L.shift(L.propositionTerm(proposition), cs.extra);
    const leftTerm = L.shift(L.propositionTerm(proposition.left), cs.extra);
    const rightTerm = L.shift(L.propositionTerm(proposition.right), cs.extra);
    const left = prove(amb, eliminateHypothesis(cs, index, proposition.left));
    if (!left.ok) return left;
    const right = prove(amb, eliminateHypothesis(cs, index, proposition.right));
    if (!right.ok) return right;
    const motive = K.lam("_s", sumTerm, L.shift(L.propositionTerm(cs.goal), cs.extra + 1));
    return {
      ok: true,
      proof: K.SumCase(
        0,
        leftTerm,
        rightTerm,
        motive,
        K.lam("_h", leftTerm, left.proof),
        K.lam("_h", rightTerm, right.proof),
        hypothesis.proof,
      ),
      multipliers: left.multipliers ?? right.multipliers,
      path: cs.path,
    };
  }
  if (proposition.kind === "not" && proposition.inner.kind === "eq" && isIntTerm(proposition.inner.type)) {
    return splitDisequality(amb, cs, index, proposition.inner);
  }
  return undefined;
}

/** `a !== b` (with `hneq : Not (Eq Int a b)`) as the two cases `a < b` and `b < a`. */
function splitDisequality(
  amb: Ambience,
  cs: Case,
  index: number,
  equality: { readonly lhs: K.Term; readonly rhs: K.Term },
): ProofOutcome {
  const extra = cs.extra;
  const hneq = cs.hyps[index]!.proof;
  const a = L.shift(equality.lhs, extra);
  const b = L.shift(equality.rhs, extra);
  // `yes`: hle : Le a b, and `a < b` follows because `a = b` would refute the disequality.
  const aBelow = L.shift(equality.lhs, extra + 1);
  const bBelow = L.shift(equality.rhs, extra + 1);
  const derived = K.ByContra(
    K.Add(aBelow, K.intLit(1n)),
    bBelow,
    K.lam(
      "_k",
      K.Lt(bBelow, K.Add(aBelow, K.intLit(1n))),
      K.app(
        L.shift(hneq, 2),
        // `Lt b (a + 1)` is convertible to `Le b a`, so it fits `intEq`'s second proof.
        K.IntEq(L.shift(equality.lhs, extra + 2), L.shift(equality.rhs, extra + 2), K.varTerm(1), K.varTerm(0)),
      ),
    ),
  );
  const leText = `${K.formatTerm(equality.lhs)} <= ${K.formatTerm(equality.rhs)}`;
  const ltText = `${K.formatTerm(equality.lhs)} < ${K.formatTerm(equality.rhs)}`;
  const yesCase: Case = {
    hyps: [
      ...cs.hyps
        .filter((_, at) => at !== index)
        .map((other) => ({ ...other, proof: L.shift(other.proof, 1) })),
      { proposition: { kind: "le", lhs: equality.lhs, rhs: equality.rhs }, proof: K.varTerm(0), text: leText },
      {
        proposition: { kind: "le", lhs: K.Add(equality.lhs, K.intLit(1n)), rhs: equality.rhs },
        proof: derived,
        text: ltText,
      },
    ],
    goal: cs.goal,
    extra: extra + 1,
    path: [...cs.path, ltText],
  };
  const yes = prove(amb, yesCase);
  if (!yes.ok) return yes;
  const negated: L.Proposition = { kind: "le", lhs: K.Add(equality.rhs, K.intLit(1n)), rhs: equality.lhs };
  const no = prove(amb, eliminateHypothesis(cs, index, negated));
  if (!no.ok) return no;
  return {
    ok: true,
    proof: K.IfLe(
      0,
      L.shift(L.propositionTerm(cs.goal), extra),
      a,
      b,
      K.lam("_h", K.Le(a, b), yes.proof),
      K.lam("_h", K.Lt(b, a), no.proof),
    ),
    multipliers: yes.multipliers ?? no.multipliers,
    path: cs.path,
  };
}

function isIntTerm(term: K.Term): boolean {
  return term.tag === "Prim" && term.op === K.OP_INT;
}

function proveNegation(amb: Ambience, cs: Case): ProofOutcome {
  if (cs.goal.kind !== "not") return unreachable(cs);
  const inner = cs.goal.inner;
  const extended = addHypothesis(cs, inner, L.propositionText(inner));
  const sub = prove(amb, { ...extended, goal: { kind: "empty" } });
  if (!sub.ok) return absurdFallback(amb, cs, sub.reason);
  return {
    ok: true,
    proof: K.lam("_h", L.shift(L.propositionTerm(inner), cs.extra), sub.proof),
    multipliers: sub.multipliers,
    path: cs.path,
  };
}

/**
 * The last resort for any goal: if the hypotheses alone are contradictory, prove them
 * false and eliminate `Empty`. Keeps the goal-directed failure reason when they are not.
 */
function absurdFallback(amb: Ambience, cs: Case, reason: string): ProofOutcome {
  const contradiction = proveEmpty(amb, cs);
  if (!contradiction.ok) return { ok: false, reason, path: cs.path };
  return {
    ok: true,
    proof: K.Absurd(0, L.shift(L.propositionTerm(cs.goal), cs.extra), contradiction.proof),
    multipliers: contradiction.multipliers,
    path: cs.path,
  };
}

function unreachable(cs: Case): ProofOutcome {
  return { ok: false, reason: `internal: goal kind mismatch (${cs.goal.kind})`, path: cs.path };
}

// ---------------------------------------------------------------------------
// Z3 queries
// ---------------------------------------------------------------------------

type CertificateOutcome = { readonly ok: true; readonly lambda: bigint[] } | { readonly ok: false; readonly error: string };

/** The multiplier search of section 6.4, verified against `linear.ts`'s own checker. */
function findCertificate(
  amb: Ambience,
  rows: readonly L.Row[],
  printed: readonly S.PrintedRow[],
): CertificateOutcome {
  if (rows.length === 0) return { ok: false, error: "there are no rows to certify" };
  const request = { env: amb.env, depth: amb.depth, rows: printed, atomTable: amb.atoms };
  const probe = S.printCertificateQuery(request, "sat");
  debug("certificate query:\n" + probe.script);
  const reply = Z.evalScript(probe.script, { timeoutMs: amb.timeoutMs });
  debug("certificate reply ok=" + reply.ok + " err=" + (reply.error ?? "-") + "\n" + reply.output);
  if (!reply.ok) return { ok: false, error: reply.error ?? "the certificate query failed" };
  const verdict = S.parseVerdict(reply.output);
  if (verdict === "unknown") {
    return { ok: false, error: "Z3 returned unknown for the certificate query (timeout)" };
  }
  if (verdict !== "sat") return { ok: false, error: "no Farkas certificate exists for the tightened rows" };
  const query = S.printCertificateQuery(request, "values");
  const valuesReply = Z.evalScript(query.script, { timeoutMs: amb.timeoutMs });
  if (!valuesReply.ok) {
    return { ok: false, error: valuesReply.error ?? "the multiplier query failed" };
  }
  const values = S.decodeValues(valuesReply.output, query.multipliers);
  if (values === undefined) {
    return { ok: false, error: `could not read the multipliers from Z3's answer: ${valuesReply.output}` };
  }
  const lambda = query.multipliers.map((name) => BigInt(values[name]!));
  if (!L.checkCertificate(rows, lambda)) {
    return { ok: false, error: `the multipliers Z3 returned do not check: [${lambda.join(", ")}]` };
  }
  return { ok: true, lambda };
}

/** Assert the hypotheses and the negated goal; on `sat`, fetch a model. */
function checkValidity(
  amb: Ambience,
  hypotheses: readonly L.Proposition[],
  goal: L.Proposition,
): ValidityOutcome {
  const query = S.printObligation({
    env: amb.env,
    depth: amb.depth,
    hypotheses,
    goal,
    atomTable: amb.atoms,
  });
  if (!query.complete) {
    // The hypotheses and the goal are printed as propositions, so the query is only a
    // faithful statement of the obligation when every one of them has an encoding. A
    // dropped hypothesis could make a `sat` answer spurious, so the answer is unusable.
    return { kind: "unknown", reason: "part of the obligation is outside the SMT encoding" };
  }
  const reply = Z.evalScript(query.script, { timeoutMs: amb.timeoutMs });
  if (!reply.ok) return { kind: "unknown", reason: reply.error ?? "the Z3 query failed" };
  const verdict = S.parseVerdict(reply.output);
  if (verdict === "unsat") return { kind: "valid" };
  if (verdict === "unknown") return { kind: "unknown", reason: "Z3 returned unknown (timeout)" };
  if (verdict !== "sat") {
    return { kind: "unknown", reason: `Z3 did not answer check-sat (${JSON.stringify(reply.output)})` };
  }
  const withModel = S.printObligation({
    env: amb.env,
    depth: amb.depth,
    hypotheses,
    goal,
    model: true,
    atomTable: amb.atoms,
  });
  const modelReply = Z.evalScript(withModel.script, { timeoutMs: amb.timeoutMs });
  if (!modelReply.ok) return { kind: "unknown", reason: modelReply.error ?? "the model query failed" };
  const model = S.decodeModel(modelReply.output);
  // `sat` is itself the proof that the obligation does not hold — the model is only there to
  // *explain* it, and an obligation whose goal mentions no atom (a closed false proposition)
  // has an empty model. Reporting "unknown" for it would hide a real invalidity.
  return { kind: "invalid", counterexample: counterexampleOf(amb, model) };
}

/** Turn a model over `a0`, `a1`, … into a counterexample over user-facing names. */
function counterexampleOf(amb: Ambience, model: Readonly<Record<string, string>>): Record<string, string> {
  const out: Record<string, string> = {};
  for (const entry of amb.atoms.entries()) {
    const value = model[entry.name];
    if (value === undefined) continue;
    let label = amb.atomNames[entry.key];
    if (label === undefined) {
      label =
        entry.representative !== undefined && entry.representative.tag !== "Var"
          ? K.formatTerm(entry.representative)
          : entry.key;
    }
    if (out[label] !== undefined) label = `${label} (${entry.key})`;
    out[label] = value;
  }
  return out;
}

// ---------------------------------------------------------------------------
// Kernel side of the contract
// ---------------------------------------------------------------------------

/**
 * Ask the kernel to accept the proof. Only possible when the obligation carried its
 * ambient binder types; without them the caller's own kernel check (milestone 7 checks the
 * whole elaborated term) is the trust boundary.
 */
function kernelCheck(
  amb: Ambience,
  proof: K.Term,
  goal: L.Proposition,
  obligation: Obligation,
): { readonly ok: true } | { readonly ok: false; readonly reason: string } {
  const ctx = amb.ctx;
  if (ctx === undefined) return { ok: true };
  try {
    const expected = K.evalTerm(amb.env, L.propositionTerm(goal), ctx.values);
    const result = K.check(ctx, proof, expected);
    if (result.ok) return { ok: true };
    return {
      ok: false,
      reason: `the kernel rejected the proof of ${obligation.id}: ${K.formatKernelError(result.error)}`,
    };
  } catch (cause) {
    const message = cause instanceof Error ? cause.message : String(cause);
    return { ok: false, reason: `the kernel rejected the proof of ${obligation.id}: ${message}` };
  }
}

function termsConvertible(amb: Ambience, a: K.Term, b: K.Term): boolean {
  try {
    const values = L.contextValues(amb.depth);
    const left = K.evalTerm(amb.env, a, values);
    const right = K.evalTerm(amb.env, b, values);
    return K.convValue(amb.env, amb.depth, left, right);
  } catch {
    return false;
  }
}
