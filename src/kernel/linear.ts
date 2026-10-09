/**
 * Linear normal forms over integer atoms, and the canonical atom key.
 *
 * Every value of type `Int` built from literals with `add`, `sub`, `neg` and `mulConst`
 * evaluates to a `Linear` value: a constant plus a map from atom key to coefficient
 * (`value.ts`). An atom is any other `Int` value — a variable, or a stuck built-in such as
 * `get A n v i p` — and is identified by a string key computed here.
 *
 * The key is computed *structurally*, never by quoting at the ambient depth, and it is
 * independent of where the value is used. Free variables are named by their de Bruijn
 * **level** (levels are globally fresh in this kernel); bound variables inside a closure
 * are named by their de Bruijn index relative to the traversal, so closures are compared
 * up to alpha-equivalence. Names and op tags are length-prefixed, so the encoding is
 * unambiguous and two keys are equal exactly when the two values have the same normal
 * form up to the rules conversion itself applies:
 *
 *   - proof arguments (`PrimInfo.irrelevant`) are erased, exactly as conversion erases
 *     them, so `get Int n v i p` and `get Int n v i p'` share a key;
 *   - `Farkas` certificates are all the same key (they all prove `Empty`);
 *   - `Pair` annotations are ignored (conversion ignores them);
 *   - a linear value whose form is a single atom with coefficient 1 and constant 0 keys
 *     as that atom, which is what makes `get Int (n + 0) v i p` and `get Int n v i p`
 *     share a key.
 *
 * Equality of keys therefore implies convertibility of the atoms; distinct keys never
 * identify distinct values except by *failing* to identify convertible ones (incomplete,
 * hence sound).
 */
import type { PrimOp, Term } from "./term";
import type { Head, LinearAtom, LinearForm, Value } from "./value";
import { vint, vlinear } from "./value";

/** Looks up the proof-argument mask of an op; `undefined` for ops without one. */
export type IrrelevantOf = (op: PrimOp) => readonly number[] | undefined;

// ---------------------------------------------------------------------------
// Integer arithmetic
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

/** Truncation toward zero, i.e. what `Math.trunc(a / b)` does for a positive divisor. */
export const truncDiv = (a: bigint, b: bigint): bigint => a / b;

// ---------------------------------------------------------------------------
// Forms
// ---------------------------------------------------------------------------

export const emptyForm = (k: bigint): LinearForm => ({ k, atoms: new Map() });

/** The linear form of an `Int` value: literals and linear values are already in form. */
export function formOf(value: Value, irrelevantOf: IrrelevantOf): LinearForm {
  if (value.tag === "IntLit") return emptyForm(value.value);
  if (value.tag === "Linear") return { k: value.k, atoms: value.atoms };
  const key = keyOfValue(value, irrelevantOf);
  return { k: 0n, atoms: new Map([[key, { key, coefficient: 1n, repr: value }]]) };
}

/** Back to a value: an atom-free form becomes a literal. */
export const vform = (form: LinearForm): Value => vlinear(form.k, form.atoms);

function mergeAtoms(
  a: ReadonlyMap<string, LinearAtom>,
  b: ReadonlyMap<string, LinearAtom>,
  scaleB: bigint,
): Map<string, LinearAtom> {
  const out = new Map<string, LinearAtom>(a);
  for (const [key, atom] of b) {
    const existing = out.get(key);
    const coefficient = atom.coefficient * scaleB;
    if (existing === undefined) out.set(key, { key, coefficient, repr: atom.repr });
    else out.set(key, { key, coefficient: existing.coefficient + coefficient, repr: existing.repr });
  }
  for (const [key, atom] of [...out]) {
    if (atom.coefficient === 0n) out.delete(key);
  }
  return out;
}

export const formAdd = (a: LinearForm, b: LinearForm): LinearForm => ({
  k: a.k + b.k,
  atoms: mergeAtoms(a.atoms, b.atoms, 1n),
});

export const formSub = (a: LinearForm, b: LinearForm): LinearForm => ({
  k: a.k - b.k,
  atoms: mergeAtoms(a.atoms, b.atoms, -1n),
});

export const formNeg = (a: LinearForm): LinearForm => formScale(a, -1n);

export function formScale(a: LinearForm, factor: bigint): LinearForm {
  if (factor === 0n) return emptyForm(0n);
  const atoms = new Map<string, LinearAtom>();
  for (const [key, atom] of a.atoms) {
    atoms.set(key, { key, coefficient: atom.coefficient * factor, repr: atom.repr });
  }
  return { k: a.k * factor, atoms };
}

/** Two forms are the same function of the atoms: same constant, same coefficients. */
export function formEquals(a: LinearForm, b: LinearForm): boolean {
  if (a.k !== b.k || a.atoms.size !== b.atoms.size) return false;
  for (const [key, atom] of a.atoms) {
    if (b.atoms.get(key)?.coefficient !== atom.coefficient) return false;
  }
  return true;
}

// ---------------------------------------------------------------------------
// Canonical keys
// ---------------------------------------------------------------------------

/** Length-prefixed, so a name can never make two renderings collide. */
const named = (tag: string, name: string): string => `${tag}${name.length}:${name}`;

/** The canonical text of a form: this is the key of a `Linear` value. */
export function formKeyText(form: LinearForm): string {
  if (form.atoms.size === 0) return `Intlit(${form.k})`;
  if (form.k === 0n && form.atoms.size === 1) {
    const only = [...form.atoms.values()][0]!;
    if (only.coefficient === 1n) return only.key;
  }
  const entries = [...form.atoms.entries()]
    .map(([key, atom]) => `${key}*${atom.coefficient}`)
    .sort()
    .join("+");
  return `Lin(${form.k};${entries})`;
}

const argsText = (parts: readonly string[]): string => `[${parts.join(",")}]`;

/** The canonical key of any value. See the module comment for what it identifies. */
export function keyOfValue(value: Value, irrelevantOf: IrrelevantOf): string {
  return keyValue(value, 0, irrelevantOf, "");
}

/**
 * Binders of a value spliced in from a closure's environment are named in a namespace of
 * their own.  Without it, a binder inside such a value and a binder of the term being
 * traversed could print the same `Bound(n)`, which would make two *different* values key
 * equally — and equal keys make `Le` conversion identify non-equivalent propositions, which
 * would let `Farkas` prove `Empty` (a soundness hole, not merely a completeness one).
 */
const SUBSTITUTED = "\u0001";

function keyValue(value: Value, depth: number, irrelevantOf: IrrelevantOf, ns: string): string {
  switch (value.tag) {
    case "Sort":
      return `Sort(${value.level})`;
    case "IntLit":
      return `Intlit(${value.value})`;
    case "Linear":
      return formKeyText({ k: value.k, atoms: value.atoms });
    case "Farkas":
      return "Proof";
    case "Pair":
      // The Sigma annotation is a type; conversion ignores it, so the key ignores it too.
      return `Pair(${keyValue(value.first, depth, irrelevantOf, ns)},${keyValue(value.second, depth, irrelevantOf, ns)})`;
    case "Pi":
      return `Pi(${keyValue(value.domain, depth, irrelevantOf, ns)},${keyClosure(value.codomain, depth, irrelevantOf, ns)})`;
    case "Lam":
      return `Lam(${keyValue(value.domain, depth, irrelevantOf, ns)},${keyClosure(value.body, depth, irrelevantOf, ns)})`;
    case "Sigma":
      return `Sig(${keyValue(value.first, depth, irrelevantOf, ns)},${keyClosure(value.second, depth, irrelevantOf, ns)})`;
    case "Neutral": {
      const head = keyHead(value.head, depth, irrelevantOf, ns);
      if (value.spine.length === 0) return head;
      return `${head}(${value.spine.map((arg) => keyValue(arg, depth, irrelevantOf, ns)).join(",")})`;
    }
  }
}

function keyClosure(
  closure: { readonly body: Term; readonly env: readonly Value[] },
  depth: number,
  irrelevantOf: IrrelevantOf,
  ns: string,
): string {
  return keyTerm(closure.body, closure.env, depth + 1, 0, irrelevantOf, ns);
}

function keyHead(head: Head, depth: number, irrelevantOf: IrrelevantOf, ns: string): string {
  switch (head.tag) {
    case "Var":
      return `Var(${head.level})`;
    case "Const":
      return named("Const", head.name);
    case "Fst":
      return `Fst(${keyValue(head.pair, depth, irrelevantOf, ns)})`;
    case "Snd":
      return `Snd(${keyValue(head.pair, depth, irrelevantOf, ns)})`;
    case "Prim": {
      const mask = irrelevantOf(head.op);
      const parts = head.args.map((arg, index) =>
        mask !== undefined && mask.includes(index) ? "_" : keyValue(arg, depth, irrelevantOf, ns),
      );
      return `Prim(${head.level}:${named("", head.op)})${argsText(parts)}`;
    }
  }
}

/**
 * The key of a term that lives inside a closure, e.g. the body of a `Lam` value. `depth`
 * counts the binders the traversal has introduced, *including* this closure's own
 * parameter; `local` counts the binders inside this term; `env` gives the values of the
 * free variables the closure was created under; `ns` namespaces the binders of values
 * spliced in from `env` (see `SUBSTITUTED`).  A de Bruijn index therefore means one of:
 *
 *   - `< local`: a binder inside this term, named by its index relative to the traversal;
 *   - `=== local`: the closure's parameter, named by the traversal depth;
 *   - `> local`: a variable of the closure's environment, substituted by its value, which
 *     lives outside this closure and is therefore keyed at the canonical depth 0 (so the
 *     same value keys the same however deep it is substituted).
 *
 * Names never depend on how deep the value happens to be used, so two values that differ
 * only in the levels of their bound variables key the same, and two that differ in what a
 * bound variable *means* key differently.
 */
function keyTerm(
  term: Term,
  env: readonly Value[],
  depth: number,
  local: number,
  irrelevantOf: IrrelevantOf,
  ns: string,
): string {
  const bound = (index: number): string => `Bound(${ns}${depth + local - 1 - index})`;
  const sub = (t: Term, extra: number): string => keyTerm(t, env, depth, local + extra, irrelevantOf, ns);
  switch (term.tag) {
    case "Var": {
      if (term.index < local) return bound(term.index);
      const outer = term.index - local;
      if (outer === 0) return `Bound(${ns}${depth - 1})`;
      const slot = env.length - outer;
      const value = slot >= 0 && slot < env.length ? env[slot] : undefined;
      if (value === undefined) return `Free(${term.index})`;
      return keyValue(value, 0, irrelevantOf, ns === "" ? SUBSTITUTED : ns);
    }
    case "Sort":
      return `Sort(${term.level})`;
    case "IntLit":
      return `Intlit(${term.value})`;
    case "Const":
      return named("Const", term.name);
    case "Farkas":
      return "Proof";
    case "App":
      return `App(${sub(term.fn, 0)},${sub(term.arg, 0)})`;
    case "Pi":
      return `Pi(${sub(term.domain, 0)},${sub(term.body, 1)})`;
    case "Lam":
      return `Lam(${sub(term.domain, 0)},${sub(term.body, 1)})`;
    case "Sigma":
      return `Sig(${sub(term.first, 0)},${sub(term.second, 1)})`;
    case "Pair":
      return `Pair(${sub(term.first, 0)},${sub(term.second, 0)})`;
    case "Fst":
      return `Fst(${sub(term.pair, 0)})`;
    case "Snd":
      return `Snd(${sub(term.pair, 0)})`;
    case "Let":
      return `Let(${sub(term.type, 0)},${sub(term.value, 0)},${sub(term.body, 1)})`;
    case "Prim": {
      const mask = irrelevantOf(term.op);
      const parts = term.args.map((arg, index) =>
        mask !== undefined && mask.includes(index) ? "_" : sub(arg, 0),
      );
      return `Prim(${term.level ?? 0}:${named("", term.op)})${argsText(parts)}`;
    }
  }
}
