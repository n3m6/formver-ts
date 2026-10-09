/**
 * Linear normalization, GCD tightening, row algebra and case splitting (specification 6.4).
 *
 * This module **deliberately duplicates** the kernel's arithmetic: `tightenRow`,
 * `checkCertificate` and `rowOfLe` mirror `src/kernel/farkas.ts` exactly, and the form
 * arithmetic mirrors `src/kernel/linear.ts`/`value.ts`. The kernel cannot import this file
 * and this file must not call the kernel's copies, so that a bug here shows up as a
 * rejected certificate rather than as a silently weakened kernel. What *is* shared, on
 * purpose, are the two definitions that must never diverge:
 *
 *   - `K.keyOfValue` decides atom identity (the canonical key string), so this module and
 *     the kernel always cancel the same atoms;
 *   - `K.formOf` turns an evaluated `Int` value into a linear form, so "what is linear"
 *     is decided in one place.
 *
 * Everything on top of those — merging forms, extraction of `Le` rows, tightening,
 * certificate checking, case splitting — is implemented here.
 *
 * Rows are `Σ aᵢ·xᵢ <= b` over integer-valued atoms. A hypothesis `s <= t` gives the row of
 * the linear form of `s - t` with `b = -k` (the form's constant), exactly like the kernel.
 */
import * as K from "../kernel/index";

// ---------------------------------------------------------------------------
// Integer arithmetic (duplicated from src/kernel/linear.ts on purpose)
// ---------------------------------------------------------------------------

/** Non-negative greatest common divisor; `gcd(0, 0) = 0`. */
export function gcd(a: bigint, b: bigint): bigint {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) {
    const next = x % y;
    x = y;
    y = next;
  }
  return x;
}

/** Floor division for a positive divisor (`bigint` division truncates toward zero). */
export function floorDiv(a: bigint, b: bigint): bigint {
  const quotient = a / b;
  const remainder = a % b;
  return remainder !== 0n && remainder < 0n ? quotient - 1n : quotient;
}

// ---------------------------------------------------------------------------
// Forms
// ---------------------------------------------------------------------------

/** One atom of a linear form: its canonical key, coefficient and a representative value. */
export interface Atom {
  readonly key: string;
  readonly coefficient: bigint;
  readonly repr: K.Value;
}

/** A linear form: a constant plus a map from atom key to atom, with no zero coefficients. */
export interface Form {
  readonly k: bigint;
  readonly atoms: ReadonlyMap<string, Atom>;
}

/** The value environment that makes atom keys stable: level `i` is the variable `Var i`. */
export function contextValues(depth: number): K.Value[] {
  const values: K.Value[] = [];
  for (let level = 0; level < depth; level += 1) values.push(K.vvar(level));
  return values;
}

/** The linear form of an already-evaluated `Int` value (the kernel decides what is linear). */
export function formOfValue(value: K.Value): Form {
  const form = K.formOf(value, K.irrelevantOf);
  return { k: form.k, atoms: form.atoms };
}

/** The linear form of an `Int` term evaluated in a context of `depth` binders. */
export function formOfTerm(env: K.Env, term: K.Term, depth: number): Form {
  return formOfValue(K.evalTerm(env, term, contextValues(depth)));
}

function merge(
  a: ReadonlyMap<string, Atom>,
  b: ReadonlyMap<string, Atom>,
  scale: bigint,
): Map<string, Atom> {
  const out = new Map<string, Atom>(a);
  for (const [key, atom] of b) {
    const existing = out.get(key);
    const coefficient = atom.coefficient * scale;
    if (existing === undefined) out.set(key, { key, coefficient, repr: atom.repr });
    else out.set(key, { key, coefficient: existing.coefficient + coefficient, repr: existing.repr });
  }
  for (const [key, atom] of [...out]) {
    if (atom.coefficient === 0n) out.delete(key);
  }
  return out;
}

export const formAdd = (a: Form, b: Form): Form => ({ k: a.k + b.k, atoms: merge(a.atoms, b.atoms, 1n) });
export const formSub = (a: Form, b: Form): Form => ({ k: a.k - b.k, atoms: merge(a.atoms, b.atoms, -1n) });
export const formNeg = (a: Form): Form => formScale(a, -1n);

export function formScale(a: Form, factor: bigint): Form {
  if (factor === 0n) return { k: 0n, atoms: new Map() };
  const atoms = new Map<string, Atom>();
  for (const [key, atom] of a.atoms) {
    atoms.set(key, { key, coefficient: atom.coefficient * factor, repr: atom.repr });
  }
  return { k: a.k * factor, atoms };
}

/** Two forms are the same function of the atoms: same constant, same coefficients. */
export function formEquals(a: Form, b: Form): boolean {
  if (a.k !== b.k || a.atoms.size !== b.atoms.size) return false;
  for (const [key, atom] of a.atoms) {
    if (b.atoms.get(key)?.coefficient !== atom.coefficient) return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

/** A linear row `Σ aᵢ·xᵢ <= b` over integer-valued atoms, in the kernel's exact shape. */
export interface Row {
  readonly a: Readonly<Record<string, bigint>>;
  readonly b: bigint;
}

/** The linear form of `lhs - rhs`, which is what a `Le lhs rhs` row is made of. */
export function formOfDifference(env: K.Env, depth: number, lhs: K.Term, rhs: K.Term): Form {
  // `K.formOf` turns a linear *value* into a form; the subtraction is this module's.
  return formSub(formOfTerm(env, lhs, depth), formOfTerm(env, rhs, depth));
}

/** A form as a row: coefficients by atom key, bound `-k`. */
export function rowOfForm(form: Form): Row {
  const a: Record<string, bigint> = {};
  for (const [key, atom] of form.atoms) a[key] = atom.coefficient;
  return { a, b: -form.k };
}

/** The row of `lhs <= rhs`: `lhs - rhs <= 0`, i.e. the form of `lhs - rhs` negated. */
export function rowOfLeTerms(env: K.Env, depth: number, lhs: K.Term, rhs: K.Term): Row {
  return rowOfForm(formOfDifference(env, depth, lhs, rhs));
}

/**
 * The row of a hypothesis whose type's weak head normal form is `Le s t`, or `undefined`
 * when the value is not a `Le`. Mirrors `src/kernel/farkas.ts`'s `rowOfLe`. A value already
 * carries its own variable levels, so nothing is evaluated here.
 */
export function rowOfValue(value: K.Value): Row | undefined {
  const head = constructorPrim(value);
  if (head === undefined || head.op !== K.OP_LE || head.args.length !== 2) return undefined;
  const form = formSub(formOfValue(head.args[0]!), formOfValue(head.args[1]!));
  const a: Record<string, bigint> = {};
  for (const [key, atom] of form.atoms) a[key] = atom.coefficient;
  return { a, b: -form.k };
}

/**
 * Integer tightening: divide every coefficient by the GCD of the non-zero coefficients and
 * floor the bound. Sound because atoms are integer-valued. Deliberately identical to the
 * kernel's `tightenRow`, including "drop zero coefficients" and "leave GCD ≤ 1 alone".
 */
export function tightenRow(row: Row): Row {
  const coefficients = new Map<string, bigint>();
  for (const [atom, coefficient] of Object.entries(row.a)) {
    if (coefficient !== 0n) coefficients.set(atom, coefficient);
  }
  let divisor = 0n;
  for (const coefficient of coefficients.values()) divisor = gcd(divisor, coefficient);
  if (divisor <= 1n) return { a: Object.fromEntries(coefficients), b: row.b };
  const tightened = new Map<string, bigint>();
  for (const [atom, coefficient] of coefficients) tightened.set(atom, coefficient / divisor);
  return { a: Object.fromEntries(tightened), b: floorDiv(row.b, divisor) };
}

/**
 * `rows` must already be tightened. Accepts when the multipliers are non-negative, cancel
 * every atom, and leave a negative bound. Deliberately identical to the kernel's
 * `checkCertificate`.
 */
export function checkCertificate(rows: readonly Row[], coefficients: readonly bigint[]): boolean {
  if (coefficients.length !== rows.length) return false;
  const total = new Map<string, bigint>();
  let bound = 0n;
  for (let i = 0; i < rows.length; i += 1) {
    const multiplier = coefficients[i]!;
    if (multiplier < 0n) return false;
    const row = rows[i]!;
    for (const [atom, coefficient] of Object.entries(row.a)) {
      total.set(atom, (total.get(atom) ?? 0n) + multiplier * coefficient);
    }
    bound += multiplier * row.b;
  }
  for (const coefficient of total.values()) {
    if (coefficient !== 0n) return false;
  }
  return bound < 0n;
}

/** Structural equality of rows, used by the agreement tests against the kernel. */
export function rowEquals(a: Row, b: Row): boolean {
  const left = Object.entries(a.a).filter(([, c]) => c !== 0n);
  const right = Object.entries(b.a).filter(([, c]) => c !== 0n);
  if (left.length !== right.length || a.b !== b.b) return false;
  for (const [key, coefficient] of left) {
    if (b.a[key] !== coefficient) return false;
  }
  return true;
}

/** The saturated primitive a value is, if any (that is how the kernel sees a `Le`). */
export function constructorPrim(
  value: K.Value,
): { readonly op: K.PrimOp; readonly level: number; readonly args: readonly K.Value[] } | undefined {
  if (value.tag !== "Neutral" || value.spine.length !== 0) return undefined;
  return value.head.tag === "Prim" ? value.head : undefined;
}

// ---------------------------------------------------------------------------
// de Bruijn plumbing
// ---------------------------------------------------------------------------

/**
 * Shift the free variables of a term by `by`. `cutoff` counts the binders the traversal
 * has entered, so `shift(term, 1, 0)` lifts an ambient term under one new binder.
 */
export function shift(term: K.Term, by: number, cutoff = 0): K.Term {
  if (by === 0) return term;
  const under = (t: K.Term): K.Term => shift(t, by, cutoff + 1);
  switch (term.tag) {
    case "Var":
      return term.index < cutoff ? term : { tag: "Var", index: term.index + by };
    case "Sort":
    case "IntLit":
    case "Const":
      return term;
    case "Pi":
      return { tag: "Pi", name: term.name, domain: shift(term.domain, by, cutoff), body: under(term.body) };
    case "Lam":
      return { tag: "Lam", name: term.name, domain: shift(term.domain, by, cutoff), body: under(term.body) };
    case "Sigma":
      return {
        tag: "Sigma",
        name: term.name,
        first: shift(term.first, by, cutoff),
        second: under(term.second),
      };
    case "App":
      return { tag: "App", fn: shift(term.fn, by, cutoff), arg: shift(term.arg, by, cutoff) };
    case "Pair":
      return {
        tag: "Pair",
        sigma: shift(term.sigma, by, cutoff),
        first: shift(term.first, by, cutoff),
        second: shift(term.second, by, cutoff),
      };
    case "Fst":
      return { tag: "Fst", pair: shift(term.pair, by, cutoff) };
    case "Snd":
      return { tag: "Snd", pair: shift(term.pair, by, cutoff) };
    case "Let":
      return {
        tag: "Let",
        name: term.name,
        type: shift(term.type, by, cutoff),
        value: shift(term.value, by, cutoff),
        body: under(term.body),
      };
    case "Prim":
      return term.level === undefined
        ? { tag: "Prim", op: term.op, args: term.args.map((arg) => shift(arg, by, cutoff)) }
        : {
            tag: "Prim",
            op: term.op,
            level: term.level,
            args: term.args.map((arg) => shift(arg, by, cutoff)),
          };
    case "Farkas":
      return { tag: "Farkas", hyps: term.hyps.map((hyp) => shift(hyp, by, cutoff)), coeffs: [...term.coeffs] };
  }
}

/** The largest de Bruijn index in `term` that is free in it; `-1` when there is none. */
export function maxFreeIndex(term: K.Term): number {
  let max = -1;
  const visit = (t: K.Term, depth: number): void => {
    switch (t.tag) {
      case "Var":
        if (t.index >= depth) max = Math.max(max, t.index - depth);
        return;
      case "Sort":
      case "IntLit":
      case "Const":
        return;
      case "Pi":
      case "Lam":
      case "Sigma":
        visit(t.tag === "Sigma" ? t.first : t.domain, depth);
        visit(t.tag === "Sigma" ? t.second : t.body, depth + 1);
        return;
      case "App":
        visit(t.fn, depth);
        visit(t.arg, depth);
        return;
      case "Pair":
        visit(t.sigma, depth);
        visit(t.first, depth);
        visit(t.second, depth);
        return;
      case "Fst":
        visit(t.pair, depth);
        return;
      case "Snd":
        visit(t.pair, depth);
        return;
      case "Let":
        visit(t.type, depth);
        visit(t.value, depth);
        visit(t.body, depth + 1);
        return;
      case "Prim":
        for (const arg of t.args) visit(arg, depth);
        return;
      case "Farkas":
        for (const hyp of t.hyps) visit(hyp, depth);
        return;
    }
  };
  visit(term, 0);
  return max;
}

/** True when the variable at de Bruijn `index` (relative to the term's binders) occurs. */
export function occursFree(term: K.Term, index: number): boolean {
  let found = false;
  const visit = (t: K.Term, depth: number): void => {
    if (found) return;
    switch (t.tag) {
      case "Var":
        if (t.index === index + depth) found = true;
        return;
      case "Sort":
      case "IntLit":
      case "Const":
        return;
      case "Pi":
      case "Lam":
      case "Sigma":
        visit(t.tag === "Sigma" ? t.first : t.domain, depth);
        visit(t.tag === "Sigma" ? t.second : t.body, depth + 1);
        return;
      case "App":
        visit(t.fn, depth);
        visit(t.arg, depth);
        return;
      case "Pair":
        visit(t.sigma, depth);
        visit(t.first, depth);
        visit(t.second, depth);
        return;
      case "Fst":
        visit(t.pair, depth);
        return;
      case "Snd":
        visit(t.pair, depth);
        return;
      case "Let":
        visit(t.type, depth);
        visit(t.value, depth);
        visit(t.body, depth + 1);
        return;
      case "Prim":
        for (const arg of t.args) visit(arg, depth);
        return;
      case "Farkas":
        for (const hyp of t.hyps) visit(hyp, depth);
        return;
    }
  };
  visit(term, 0);
  return found;
}

/**
 * Drop `count` binders: every free variable of `term` moves down by `count`. Used to read a
 * non-dependent `Sigma`/`Pi` body out of its binder (see `propositionOfValue`), and to turn
 * a proposition written in a full context into a binder domain: the domain of the binder at
 * position `p` of a `d`-binder context lives in the context of the `p` binders before it,
 * so its variables move down by `d - p` (the kernel's `Ctx` stores exactly that).
 */
export function dropBinders(term: K.Term, count: number): K.Term {
  if (count <= 0) return term;
  const visit = (t: K.Term, depth: number): K.Term => {
    const under = (x: K.Term): K.Term => visit(x, depth + 1);
    switch (t.tag) {
      case "Var":
        return t.index <= depth ? t : { tag: "Var", index: t.index - count };
      case "Sort":
      case "IntLit":
      case "Const":
        return t;
      case "Pi":
        return { tag: "Pi", name: t.name, domain: visit(t.domain, depth), body: under(t.body) };
      case "Lam":
        return { tag: "Lam", name: t.name, domain: visit(t.domain, depth), body: under(t.body) };
      case "Sigma":
        return { tag: "Sigma", name: t.name, first: visit(t.first, depth), second: under(t.second) };
      case "App":
        return { tag: "App", fn: visit(t.fn, depth), arg: visit(t.arg, depth) };
      case "Pair":
        return {
          tag: "Pair",
          sigma: visit(t.sigma, depth),
          first: visit(t.first, depth),
          second: visit(t.second, depth),
        };
      case "Fst":
        return { tag: "Fst", pair: visit(t.pair, depth) };
      case "Snd":
        return { tag: "Snd", pair: visit(t.pair, depth) };
      case "Let":
        return {
          tag: "Let",
          name: t.name,
          type: visit(t.type, depth),
          value: visit(t.value, depth),
          body: under(t.body),
        };
      case "Prim":
        return t.level === undefined
          ? { tag: "Prim", op: t.op, args: t.args.map((arg) => visit(arg, depth)) }
          : { tag: "Prim", op: t.op, level: t.level, args: t.args.map((arg) => visit(arg, depth)) };
      case "Farkas":
        return { tag: "Farkas", hyps: t.hyps.map((hyp) => visit(hyp, depth)), coeffs: [...t.coeffs] };
    }
  };
  return visit(term, 0);
}

/**
 * Drop one binder: every free variable strictly inside `term` moves down by one. A special
 * case of `dropBinders` kept for readability where a single `Sigma`/`Pi` body is read out.
 */
export function unbind(term: K.Term): K.Term {
  return dropBinders(term, 1);
}

// ---------------------------------------------------------------------------
// Propositions
// ---------------------------------------------------------------------------

/**
 * A proposition in the shapes the fragment can produce, normalized out of a kernel value.
 * Anything else is `other` and is never turned into a certificate; it can only be dropped
 * (sound, just incomplete) or reported.
 */
export type Proposition =
  | { readonly kind: "unit" }
  | { readonly kind: "empty" }
  | { readonly kind: "le"; readonly lhs: K.Term; readonly rhs: K.Term }
  | { readonly kind: "eq"; readonly type: K.Term; readonly lhs: K.Term; readonly rhs: K.Term }
  | { readonly kind: "and"; readonly first: Proposition; readonly second: Proposition }
  | { readonly kind: "sum"; readonly left: Proposition; readonly right: Proposition }
  | { readonly kind: "not"; readonly inner: Proposition }
  | { readonly kind: "other"; readonly term: K.Term };

/** The term of a proposition; converting it back to the caller's syntax is by conversion. */
export function propositionTerm(proposition: Proposition): K.Term {
  switch (proposition.kind) {
    case "unit":
      return K.Unit;
    case "empty":
      return K.Empty;
    case "le":
      return K.Le(proposition.lhs, proposition.rhs);
    case "eq":
      return K.Eq(proposition.type, proposition.lhs, proposition.rhs);
    case "and":
      return K.And(propositionTerm(proposition.first), propositionTerm(proposition.second));
    case "sum":
      return K.Sum(propositionTerm(proposition.left), propositionTerm(proposition.right));
    case "not":
      return K.Not(propositionTerm(proposition.inner));
    case "other":
      return proposition.term;
  }
}

/** The value of a proposition in a context of `depth` binders. */
export function propositionValue(env: K.Env, depth: number, proposition: Proposition): K.Value {
  return K.evalTerm(env, propositionTerm(proposition), contextValues(depth));
}

/** Structural decomposition of a proposition value. */
export function propositionOfValue(env: K.Env, depth: number, value: K.Value): Proposition {
  const head = constructorPrim(value);
  if (head !== undefined) {
    switch (head.op) {
      case K.OP_LE:
        if (head.args.length === 2) {
          return {
            kind: "le",
            lhs: K.quote(env, depth, head.args[0]!),
            rhs: K.quote(env, depth, head.args[1]!),
          };
        }
        break;
      case K.OP_EQ:
        if (head.args.length === 3) {
          return {
            kind: "eq",
            type: K.quote(env, depth, head.args[0]!),
            lhs: K.quote(env, depth, head.args[1]!),
            rhs: K.quote(env, depth, head.args[2]!),
          };
        }
        break;
      case K.OP_SUM:
        if (head.args.length === 2) {
          return {
            kind: "sum",
            left: propositionOfValue(env, depth, head.args[0]!),
            right: propositionOfValue(env, depth, head.args[1]!),
          };
        }
        break;
      case K.OP_UNIT:
        return { kind: "unit" };
      case K.OP_EMPTY:
        return { kind: "empty" };
      default:
        break;
    }
  }
  if (value.tag === "Sigma") {
    // `And A B` unfolds to a (non-dependent) `Sigma`. A genuinely dependent `Sigma` is not
    // a fragment proposition, so it stays `other` rather than being misread.
    const quoted = K.quote(env, depth, value);
    if (quoted.tag === "Sigma" && !occursFree(quoted.second, 0)) {
      return {
        kind: "and",
        first: propositionOfTerm(env, depth, quoted.first),
        second: propositionOfTerm(env, depth, unbind(quoted.second)),
      };
    }
  } else if (value.tag === "Pi") {
    // `Not A` unfolds to `A -> Empty`.
    const quoted = K.quote(env, depth, value);
    if (quoted.tag === "Pi") {
      const body = quoted.body;
      const isEmpty = body.tag === "Prim" && body.op === K.OP_EMPTY;
      if (isEmpty) return { kind: "not", inner: propositionOfTerm(env, depth, quoted.domain) };
    }
  }
  return { kind: "other", term: K.quote(env, depth, value) };
}

/** Structural decomposition of a proposition term evaluated in a context of `depth`. */
export function propositionOfTerm(env: K.Env, depth: number, term: K.Term): Proposition {
  return propositionOfValue(env, depth, K.evalTerm(env, term, contextValues(depth)));
}

/** Every `Le` boundary inside a proposition, as candidate `ifLe` operands for `||` goals. */
export function comparisonCandidates(proposition: Proposition): { lhs: K.Term; rhs: K.Term }[] {
  const out: { lhs: K.Term; rhs: K.Term }[] = [];
  const visit = (p: Proposition): void => {
    switch (p.kind) {
      case "le":
        out.push({ lhs: p.lhs, rhs: p.rhs });
        return;
      case "eq":
        if (p.type.tag === "Prim" && p.type.op === K.OP_INT) {
          out.push({ lhs: p.lhs, rhs: p.rhs });
          out.push({ lhs: p.rhs, rhs: p.lhs });
        }
        return;
      case "and":
        visit(p.first);
        visit(p.second);
        return;
      case "sum":
        visit(p.left);
        visit(p.right);
        return;
      case "not":
        visit(p.inner);
        return;
      default:
        return;
    }
  };
  visit(proposition);
  return out;
}

/** A short human-readable rendering of a proposition, for diagnostics and case paths. */
export function propositionText(proposition: Proposition): string {
  switch (proposition.kind) {
    case "unit":
      return "true";
    case "empty":
      return "false";
    case "le":
      return `${K.formatTerm(proposition.lhs)} <= ${K.formatTerm(proposition.rhs)}`;
    case "eq":
      return `${K.formatTerm(proposition.lhs)} === ${K.formatTerm(proposition.rhs)}`;
    case "and":
      return `(${propositionText(proposition.first)} && ${propositionText(proposition.second)})`;
    case "sum":
      return `(${propositionText(proposition.left)} || ${propositionText(proposition.right)})`;
    case "not":
      return `!(${propositionText(proposition.inner)})`;
    case "other":
      return K.formatTerm(proposition.term);
  }
}

/** Rows a proposition contributes, each with the proof term the kernel will see for it. */
export interface RowEntry {
  readonly row: Row;
  /** The atoms of the row, with their representatives, so SMT printing can name them. */
  readonly atoms: ReadonlyMap<string, Atom>;
  readonly proof: K.Term;
  readonly text: string;
  /** The proof's type is `Le s t`; kept for diagnostics and tests. */
  readonly proposition: Proposition;
}

export interface Linearized {
  readonly entries: readonly RowEntry[];
  /** False when part of the proposition could not be encoded as rows. */
  readonly complete: boolean;
  /** Propositions that must be case-split (or dropped) before a certificate can be found. */
  readonly residual: readonly Proposition[];
}

/** `le`-reflexivity as a kernel term: `byContra a a (k => Farkas [k] [1])`, for any `a`. */
export function leRefl(lhs: K.Term, rhs: K.Term | undefined = undefined): K.Term {
  const other = rhs ?? lhs;
  return K.ByContra(
    lhs,
    other,
    K.lam("_k", K.Lt(other, lhs), K.Farkas([K.varTerm(0)], [1n])),
  );
}

/**
 * `Le` proofs derived from an `Eq Int a b` proof by transport (`J`): an equality
 * hypothesis is only usable by `Farkas` through its two `Le` consequences.
 *
 * `J`'s motive is `fun (b' : Int) (_ : Eq Int a b') => Le a b'` with base `Le a a`; the
 * two directions differ only in which side is transported. `extra` is the number of split
 * binders the proof lives under (the proposition's terms are ambient).
 */
export function leOfEq(
  equality: { type: K.Term; lhs: K.Term; rhs: K.Term },
  proof: K.Term,
  forward: boolean,
  extra: number,
): K.Term {
  const from = shift(forward ? equality.lhs : equality.rhs, extra);
  const to = shift(forward ? equality.rhs : equality.lhs, extra);
  const shifted = shift(from, 2);
  const motive = K.lam(
    "_b",
    K.Int,
    K.lam("_h", K.Eq(K.Int, shifted, K.varTerm(1)), K.Le(shifted, K.varTerm(1))),
  );
  return K.J(0, K.Int, from, motive, leRefl(from), to, proof);
}

/**
 * Turn one hypothesis into rows. `proof` is the hypothesis's proof term in the current
 * scope; nested conjunctions are projected with `fst`/`snd`, equalities are transported to
 * their two `Le` directions. `extra` is the number of split binders around the proof; the
 * proposition's terms are ambient, so any term that ends up inside the proof is shifted.
 */
export function linearize(
  env: K.Env,
  depth: number,
  proposition: Proposition,
  proof: K.Term,
  extra: number,
): Linearized {
  const entries: RowEntry[] = [];
  const residual: Proposition[] = [];
  let complete = true;
  const visit = (p: Proposition, proofTerm: K.Term): void => {
    switch (p.kind) {
      case "le": {
        const form = formOfDifference(env, depth, p.lhs, p.rhs);
        entries.push({
          row: rowOfForm(form),
          atoms: form.atoms,
          proof: proofTerm,
          text: propositionText(p),
          proposition: p,
        });
        return;
      }
      case "eq": {
        const isInt = p.type.tag === "Prim" && p.type.op === K.OP_INT;
        if (!isInt) {
          complete = false;
          residual.push(p);
          return;
        }
        for (const forward of [true, false]) {
          const direction: Proposition = forward
            ? { kind: "le", lhs: p.lhs, rhs: p.rhs }
            : { kind: "le", lhs: p.rhs, rhs: p.lhs };
          const form = formOfDifference(env, depth, direction.lhs, direction.rhs);
          entries.push({
            row: rowOfForm(form),
            atoms: form.atoms,
            proof: leOfEq(p, proofTerm, forward, extra),
            text: propositionText(direction),
            proposition: direction,
          });
        }
        return;
      }
      case "and":
        visit(p.first, K.fst(proofTerm));
        visit(p.second, K.snd(proofTerm));
        return;
      case "unit":
        return;
      default:
        complete = false;
        residual.push(p);
        return;
    }
  };
  visit(proposition, proof);
  return { entries, complete, residual };
}
