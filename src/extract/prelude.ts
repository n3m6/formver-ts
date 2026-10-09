/**
 * The JS built-ins the verifier trusts, mapped to kernel **definitions** (specification 6.3).
 *
 * The trusted statement is only this table: `Math.max`, `Math.min`, `Math.abs`,
 * `Math.floor(e / k)` and `Math.trunc(e / k)` behave on safe integers exactly like the
 * kernel terms below.  Everything else reachable as `Math.*` is outside the fragment and
 * is rejected by `fragment.ts` with a located error.
 *
 * | surface              | kernel definition                                   |
 * |----------------------|-----------------------------------------------------|
 * | `Math.max(a, b)`     | `ifLe a b (_ => b) (_ => a)`                        |
 * | `Math.min(a, b)`     | `ifLe a b (_ => a) (_ => b)`                        |
 * | `Math.abs(x)`        | `ifLe 0 x (_ => x) (_ => -x)`                       |
 * | `Math.floor(e / k)`  | `divFloor e k`                                      |
 * | `Math.trunc(e / k)`  | `divTrunc e k`                                      |
 *
 * `Math.floor`/`Math.trunc` require the divisor to be a positive integer **literal**: the
 * kernel's `positiveLiteralArgs` hook rejects anything else, and the divisor is what makes
 * the linear encoding of division sound (specification 6.1.3).  `fragment.ts` reports the
 * located error before the kernel ever sees the term.
 *
 * The prelude is deliberately tiny: every additional entry would widen the trusted base.
 * There are **no axioms** here; `ifLe` is a primitive that reduces, `divFloor`/`divTrunc`
 * have primitive lemmas (`divFloorSpec`, `divTruncSpecNonneg`, `divTruncSpecNeg`) that
 * `fragment.ts` records as facts.
 */
import * as K from "../kernel/index";
import type { Term } from "../kernel/index";

// ---------------------------------------------------------------------------
// A shared term utility
// ---------------------------------------------------------------------------

/**
 * Shift the free de Bruijn variables of `term` up by `by`.
 *
 * Needed whenever a term built in a scope is placed under fresh binders (the branches of
 * `ifLe`, the body of a case split).  Binding is by de Bruijn index, so "building a term
 * and then wrapping it in a lambda" requires this shift; getting it wrong silently changes
 * which variable a term mentions.
 */
export function shiftTerm(term: Term, by: number): Term {
  if (by === 0) return term;
  return shiftAt(term, by, 0);
}

function shiftAt(term: Term, by: number, depth: number): Term {
  switch (term.tag) {
    case "Var":
      return term.index < depth ? term : { tag: "Var", index: term.index + by };
    case "Sort":
    case "IntLit":
    case "Const":
      return term;
    case "Pi":
      return {
        tag: "Pi",
        name: term.name,
        domain: shiftAt(term.domain, by, depth),
        body: shiftAt(term.body, by, depth + 1),
      };
    case "Lam":
      return {
        tag: "Lam",
        name: term.name,
        domain: shiftAt(term.domain, by, depth),
        body: shiftAt(term.body, by, depth + 1),
      };
    case "Sigma":
      return {
        tag: "Sigma",
        name: term.name,
        first: shiftAt(term.first, by, depth),
        second: shiftAt(term.second, by, depth + 1),
      };
    case "Let":
      return {
        tag: "Let",
        name: term.name,
        type: shiftAt(term.type, by, depth),
        value: shiftAt(term.value, by, depth),
        body: shiftAt(term.body, by, depth + 1),
      };
    case "App":
      return { tag: "App", fn: shiftAt(term.fn, by, depth), arg: shiftAt(term.arg, by, depth) };
    case "Pair":
      return {
        tag: "Pair",
        sigma: shiftAt(term.sigma, by, depth),
        first: shiftAt(term.first, by, depth),
        second: shiftAt(term.second, by, depth),
      };
    case "Fst":
      return { tag: "Fst", pair: shiftAt(term.pair, by, depth) };
    case "Snd":
      return { tag: "Snd", pair: shiftAt(term.pair, by, depth) };
    case "Prim":
      return term.level === undefined
        ? { tag: "Prim", op: term.op, args: term.args.map((arg) => shiftAt(arg, by, depth)) }
        : {
            tag: "Prim",
            op: term.op,
            level: term.level,
            args: term.args.map((arg) => shiftAt(arg, by, depth)),
          };
    case "Farkas":
      return { tag: "Farkas", hyps: term.hyps.map((hyp) => shiftAt(hyp, by, depth)), coeffs: term.coeffs };
  }
}

/** `fun (_ : domain) => body`, shifting `body` so it still mentions the same variables. */
export function lamIgnoring(name: string, domain: Term, body: Term): Term {
  return K.lam(name, domain, shiftTerm(body, 1));
}

// ---------------------------------------------------------------------------
// The table
// ---------------------------------------------------------------------------

export type MathBuiltinKind = "max" | "min" | "abs" | "floor" | "trunc";

export interface MathBuiltin {
  /** Surface name including the `Math.` prefix. */
  readonly name: string;
  readonly kind: MathBuiltinKind;
  /** Number of arguments the surface call must have. */
  readonly arity: number;
  /** True for `Math.floor` / `Math.trunc`: the single argument must be `e / k`. */
  readonly division: boolean;
  /** The kernel definition, in the notation the notes use. */
  readonly definition: string;
  /** Build the fully applied kernel term. */
  build(args: readonly Term[]): Term;
}

/** `ifLe a b (yes : Le a b -> A) (no : Lt b a -> A) : A` with the answer type `A`. */
function ifLeValue(a: Term, b: Term, yes: Term, no: Term): Term {
  return K.IfLe(0, K.Int, a, b, lamIgnoring("_", K.Le(a, b), yes), lamIgnoring("_", K.Lt(b, a), no));
}

const TABLE: ReadonlyMap<string, MathBuiltin> = new Map<string, MathBuiltin>([
  [
    "Math.max",
    {
      name: "Math.max",
      kind: "max",
      arity: 2,
      division: false,
      definition: "ifLe a b (_ => b) (_ => a)",
      build: (args) => ifLeValue(args[0]!, args[1]!, args[1]!, args[0]!),
    },
  ],
  [
    "Math.min",
    {
      name: "Math.min",
      kind: "min",
      arity: 2,
      division: false,
      definition: "ifLe a b (_ => a) (_ => b)",
      build: (args) => ifLeValue(args[0]!, args[1]!, args[0]!, args[1]!),
    },
  ],
  [
    "Math.abs",
    {
      name: "Math.abs",
      kind: "abs",
      arity: 1,
      division: false,
      definition: "ifLe 0 x (_ => x) (_ => -x)",
      build: (args) => ifLeValue(K.intLit(0n), args[0]!, args[0]!, K.Neg(args[0]!)),
    },
  ],
  [
    "Math.floor",
    {
      name: "Math.floor",
      kind: "floor",
      arity: 1,
      division: true,
      definition: "divFloor e k",
      build: (args) => K.DivFloor(args[0]!, args[1]!),
    },
  ],
  [
    "Math.trunc",
    {
      name: "Math.trunc",
      kind: "trunc",
      arity: 1,
      division: true,
      definition: "divTrunc e k",
      build: (args) => K.DivTrunc(args[0]!, args[1]!),
    },
  ],
]);

/** The prelude entry for a surface name such as `Math.floor`, if it has one. */
export function lookupMathBuiltin(name: string): MathBuiltin | undefined {
  return TABLE.get(name);
}

/** Every surface name the prelude provides, in table order. */
export function preludeNames(): string[] {
  return [...TABLE.keys()];
}
