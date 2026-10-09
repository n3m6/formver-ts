/**
 * Built-in ops: their types, reduction rules, conversion rules and the prelude
 * definitions seeded into `emptyEnv()`.
 *
 * The logic built-ins of specification section 6.1.3 are here:
 *
 *   Empty, Unit, tt, Sum (inl, inr, dependent case), absurd, Eq (refl, J)
 *
 * together with milestone 3's integer, proposition, vector and recursion built-ins:
 *
 *   Int (add, sub, neg, mulConst), Le, ifLe, byContra, intEq, And/Not/Lt/InRange (definitions),
 *   Vec (len, vecBounds, get, append, slice, castVec), fixWf, divFloor/divTrunc and their lemmas.
 *
 * Every op is one `PRIMS` entry: `name`, `arity`, `typeFor`, and optionally `reduce`
 * (absent means opaque, which is exactly how `fixWf` stays non-unfolding), `irrelevant`
 * (proof arguments ignored by conversion and by atom keys), `convArgs` (a custom
 * conversion rule, used by `Le`) and `positiveLiteralArgs` (divisors must be positive
 * integer literals).
 *
 * `And`, `Not`, `Lt` and `InRange` are *definitions*, not ops: they are inserted through
 * `addDecl` by `emptyEnv()`, which is the only insertion path and type-checks them. The
 * prelude contains zero axioms.
 *
 * `divFloorSpec`, `divTruncSpecNonneg`, `divTruncSpecNeg` and `vecBounds` are *primitive
 * lemmas*: closed ops with a type but no reduction rule and no implementation. They are
 * trusted for divisors that are positive integer literals (enforced by `check.ts` through
 * `positiveLiteralArgs`) and for vectors that only the built-in constructors can build.
 * They are deliberately not `axiom` declarations, so `axiomsUsed(emptyEnv())` stays `[]`.
 */
import type { Mk, PrimOp, Term } from "./term";
import {
  appManyMk,
  appMk,
  constMk,
  farkasMk,
  intLit,
  intLitMk,
  lamMk,
  mk,
  piMk,
  primMk,
  primTerm,
  sigmaMk,
  sortMk,
  varMk,
} from "./term";
import type { Decl } from "./env";
import { floorDiv, formAdd, formEquals, formNeg, formOf, formScale, formSub, truncDiv, vform } from "./linear";
import type { PrimInfo, Value } from "./value";
import { constructorHead, vint } from "./value";

// ---------------------------------------------------------------------------
// Op tags
// ---------------------------------------------------------------------------

export const OP_EMPTY: PrimOp = "Empty";
export const OP_UNIT: PrimOp = "Unit";
export const OP_TT: PrimOp = "tt";
export const OP_SUM: PrimOp = "Sum";
export const OP_INL: PrimOp = "inl";
export const OP_INR: PrimOp = "inr";
export const OP_CASE: PrimOp = "case";
export const OP_ABSURD: PrimOp = "absurd";
export const OP_EQ: PrimOp = "Eq";
export const OP_REFL: PrimOp = "refl";
export const OP_J: PrimOp = "J";
export const OP_INT: PrimOp = "Int";
export const OP_ADD: PrimOp = "add";
export const OP_SUB: PrimOp = "sub";
export const OP_NEG: PrimOp = "neg";
/** `mulConst k e`: multiplication by a literal. There is no product of two non-literals. */
export const OP_MUL_CONST: PrimOp = "mulConst";
/** `Le a b : Type 0`, the primitive proposition. */
export const OP_LE: PrimOp = "Le";
/** `ifLe {A} a b yes no : A`, which reduces when `a` and `b` are literals. */
export const OP_IF_LE: PrimOp = "ifLe";
/** `byContra a b (k : Lt b a -> Empty) : Le a b`. */
export const OP_BY_CONTRA: PrimOp = "byContra";
/** `intEq a b (p : Le a b) (q : Le b a) : Eq Int a b`. */
export const OP_INT_EQ: PrimOp = "intEq";
export const OP_VEC: PrimOp = "Vec";
export const OP_LEN: PrimOp = "len";
export const OP_VEC_BOUNDS: PrimOp = "vecBounds";
export const OP_GET: PrimOp = "get";
export const OP_APPEND: PrimOp = "append";
export const OP_SLICE: PrimOp = "slice";
export const OP_CAST_VEC: PrimOp = "castVec";
/** `fixWf`: well-founded recursion on an `Int` measure. Opaque: it never unfolds. */
export const OP_FIX_WF: PrimOp = "fixWf";
export const OP_DIV_FLOOR: PrimOp = "divFloor";
export const OP_DIV_FLOOR_SPEC: PrimOp = "divFloorSpec";
export const OP_DIV_TRUNC: PrimOp = "divTrunc";
export const OP_DIV_TRUNC_SPEC_NONNEG: PrimOp = "divTruncSpecNonneg";
export const OP_DIV_TRUNC_SPEC_NEG: PrimOp = "divTruncSpecNeg";

/** Names of the prelude *definitions* (specification section 6.1.3). */
export const AND_NAME = "And";
export const NOT_NAME = "Not";
/** `Lt a b := Le (a + 1) b`: strict inequality is a definition over `Le`. */
export const LT_NAME = "Lt";
/** `InRange x := And (Le (-(2^53-1)) x) (Le x (2^53-1))`. */
export const IN_RANGE_NAME = "InRange";

/** `2^53 - 1`: the largest safe integer, the bound of `InRange` (section 3.4). */
export const SAFE_MAX = 9007199254740991n;
/** `2^32 - 1`: JS's maximum array length, the bound of `vecBounds` and `append`. */
export const MAX_VEC_LEN = 4294967295n;

// ---------------------------------------------------------------------------
// Small term-building shorthands
// ---------------------------------------------------------------------------

const type0: Mk = sortMk(0);
const emptyMk: Mk = primMk(OP_EMPTY, []);
const unitMk: Mk = primMk(OP_UNIT, []);
const intMk: Mk = primMk(OP_INT, []);

const sumMk = (a: Mk, b: Mk): Mk => primMk(OP_SUM, [a, b]);
const inlMk = (a: Mk, b: Mk, x: Mk): Mk => primMk(OP_INL, [a, b, x]);
const inrMk = (a: Mk, b: Mk, x: Mk): Mk => primMk(OP_INR, [a, b, x]);
const eqMk = (a: Mk, x: Mk, y: Mk): Mk => primMk(OP_EQ, [a, x, y]);
const reflMk = (a: Mk, x: Mk): Mk => primMk(OP_REFL, [a, x]);
const appC = (fn: Mk, arg: Mk): Mk => appMk(fn, arg);

const andOf = (a: Mk, b: Mk): Mk => appManyMk(constMk(AND_NAME), [a, b]);
const ltOf = (a: Mk, b: Mk): Mk => appManyMk(constMk(LT_NAME), [a, b]);
const leOf = (a: Mk, b: Mk): Mk => primMk(OP_LE, [a, b]);
const addOf = (a: Mk, b: Mk): Mk => primMk(OP_ADD, [a, b]);
const subOf = (a: Mk, b: Mk): Mk => primMk(OP_SUB, [a, b]);
const negOf = (e: Mk): Mk => primMk(OP_NEG, [e]);
const mulConstOf = (k: Mk, e: Mk): Mk => primMk(OP_MUL_CONST, [k, e]);
const vecOf = (a: Mk, n: Mk): Mk => primMk(OP_VEC, [a, n]);
const divFloorOf = (e: Mk, k: Mk): Mk => primMk(OP_DIV_FLOOR, [e, k]);
const divTruncOf = (e: Mk, k: Mk): Mk => primMk(OP_DIV_TRUNC, [e, k]);
/** `a -> b`, the non-dependent Pi. */
const arrowOf = (a: Mk, b: Mk): Mk => piMk("_", a, b);
/** `a -> Empty`, negation. */
const notOf = (a: Mk): Mk => arrowOf(a, emptyMk);

/** Bounds-checked index into a rule's argument list; rules must tolerate a short list. */
function at(args: readonly Value[], index: number): Value | undefined {
  return index < args.length ? args[index] : undefined;
}

/** The proof-argument mask of an op, as `linear.ts` and `conv.ts` want it. */
export function irrelevantOf(op: PrimOp): readonly number[] | undefined {
  return lookupPrim(op)?.irrelevant;
}

const formOfArg = (value: Value) => formOf(value, irrelevantOf);

// ---------------------------------------------------------------------------
// The registry
// ---------------------------------------------------------------------------

/**
 * The primitive-op registry consulted by `eval.ts` (reduction), `conv.ts` (conversion)
 * and `check.ts` (typing). Frozen, so an untrusted layer cannot swap a rule at runtime.
 */
export const PRIMS: Record<string, PrimInfo> = Object.freeze({
  [OP_EMPTY]: {
    name: OP_EMPTY,
    arity: 0,
    typeFor: () => mk(type0),
  },

  [OP_UNIT]: {
    name: OP_UNIT,
    arity: 0,
    typeFor: () => mk(type0),
  },

  [OP_TT]: {
    name: OP_TT,
    arity: 0,
    typeFor: () => mk(unitMk),
  },

  /** `Sum A B : Type 0`. No core term former produces a sum, so it is primitive. */
  [OP_SUM]: {
    name: OP_SUM,
    arity: 2,
    typeFor: () => mk(piMk("A", type0, piMk("B", type0, type0))),
  },

  [OP_INL]: {
    name: OP_INL,
    arity: 3,
    typeFor: () =>
      mk(piMk("A", type0, piMk("B", type0, piMk("a", varMk("A"), sumMk(varMk("A"), varMk("B")))))),
  },

  [OP_INR]: {
    name: OP_INR,
    arity: 3,
    typeFor: () =>
      mk(piMk("A", type0, piMk("B", type0, piMk("b", varMk("B"), sumMk(varMk("A"), varMk("B")))))),
  },

  /**
   * Dependent eliminator for `Sum`:
   *   (A B : Type 0) -> (C : Sum A B -> Type l)
   *     -> ((a : A) -> C (inl A B a)) -> ((b : B) -> C (inr A B b))
   *     -> (s : Sum A B) -> C s
   * Reduces when the scrutinee is a saturated `inl`/`inr`; stuck otherwise.
   */
  [OP_CASE]: {
    name: OP_CASE,
    arity: 6,
    typeFor: (level) =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "B",
            type0,
            piMk(
              "C",
              piMk("s", sumMk(varMk("A"), varMk("B")), sortMk(level)),
              piMk(
                "onL",
                piMk("a", varMk("A"), appC(varMk("C"), inlMk(varMk("A"), varMk("B"), varMk("a")))),
                piMk(
                  "onR",
                  piMk("b", varMk("B"), appC(varMk("C"), inrMk(varMk("A"), varMk("B"), varMk("b")))),
                  piMk("s", sumMk(varMk("A"), varMk("B")), appC(varMk("C"), varMk("s"))),
                ),
              ),
            ),
          ),
        ),
      ),
    reduce: (args, ctx) => {
      const scrutinee = at(args, 5);
      if (scrutinee === undefined) return undefined;
      const head = constructorHead(scrutinee);
      if (head === undefined) return undefined;
      if (head.op === OP_INL) {
        const payload = at(head.args, 2);
        const onLeft = at(args, 3);
        return payload === undefined || onLeft === undefined ? undefined : ctx.apply(onLeft, payload);
      }
      if (head.op === OP_INR) {
        const payload = at(head.args, 2);
        const onRight = at(args, 4);
        return payload === undefined || onRight === undefined ? undefined : ctx.apply(onRight, payload);
      }
      return undefined;
    },
  },

  /**
   * `absurd A e : A` for `e : Empty`. No reduction rule: `Empty` has no canonical
   * inhabitants, so there is nothing to compute with. (A checked `Farkas` certificate does
   * inhabit `Empty`, but eliminating it is still a dead end.)
   */
  [OP_ABSURD]: {
    name: OP_ABSURD,
    arity: 2,
    typeFor: (level) => mk(piMk("A", sortMk(level), piMk("e", emptyMk, varMk("A")))),
  },

  [OP_EQ]: {
    name: OP_EQ,
    arity: 3,
    typeFor: () => mk(piMk("A", type0, piMk("a", varMk("A"), piMk("b", varMk("A"), type0)))),
  },

  [OP_REFL]: {
    name: OP_REFL,
    arity: 2,
    typeFor: () => mk(piMk("A", type0, piMk("a", varMk("A"), eqMk(varMk("A"), varMk("a"), varMk("a"))))),
  },

  /**
   * Transport (`J`):
   *   (A : Type 0) -> (a : A) -> (C : (b : A) -> Eq A a b -> Type l)
   *     -> C a (refl A a) -> (b : A) -> (p : Eq A a b) -> C b p
   * Reduces to the base case when `p` is `refl`. This is the only computation rule for
   * `Eq`; it makes equality a proposition rather than an inductive family.
   */
  [OP_J]: {
    name: OP_J,
    arity: 6,
    typeFor: (level) =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "a",
            varMk("A"),
            piMk(
              "C",
              piMk("b", varMk("A"), piMk("p", eqMk(varMk("A"), varMk("a"), varMk("b")), sortMk(level))),
              piMk(
                "d",
                appC(appC(varMk("C"), varMk("a")), reflMk(varMk("A"), varMk("a"))),
                piMk(
                  "b",
                  varMk("A"),
                  piMk(
                    "p",
                    eqMk(varMk("A"), varMk("a"), varMk("b")),
                    appC(appC(varMk("C"), varMk("b")), varMk("p")),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    reduce: (args) => {
      const proof = at(args, 5);
      if (proof === undefined) return undefined;
      const head = constructorHead(proof);
      if (head === undefined || head.op !== OP_REFL) return undefined;
      return at(args, 3);
    },
  },

  // -------------------------------------------------------------------------
  // Integers: linear normal forms (specification section 6.1.3)
  // -------------------------------------------------------------------------

  /** `Int : Type 0`. Its values are literals or linear values (`linear.ts`). */
  [OP_INT]: {
    name: OP_INT,
    arity: 0,
    typeFor: () => mk(type0),
  },

  [OP_ADD]: {
    name: OP_ADD,
    arity: 2,
    typeFor: () => mk(piMk("a", intMk, piMk("b", intMk, intMk))),
    reduce: (args) => {
      const a = at(args, 0);
      const b = at(args, 1);
      if (a === undefined || b === undefined) return undefined;
      return vform(formAdd(formOfArg(a), formOfArg(b)));
    },
  },

  [OP_SUB]: {
    name: OP_SUB,
    arity: 2,
    typeFor: () => mk(piMk("a", intMk, piMk("b", intMk, intMk))),
    reduce: (args) => {
      const a = at(args, 0);
      const b = at(args, 1);
      if (a === undefined || b === undefined) return undefined;
      return vform(formSub(formOfArg(a), formOfArg(b)));
    },
  },

  [OP_NEG]: {
    name: OP_NEG,
    arity: 1,
    typeFor: () => mk(piMk("a", intMk, intMk)),
    reduce: (args) => {
      const a = at(args, 0);
      return a === undefined ? undefined : vform(formNeg(formOfArg(a)));
    },
  },

  /** `mulConst k e` with `k` a literal; a non-literal multiplier leaves the op stuck. */
  [OP_MUL_CONST]: {
    name: OP_MUL_CONST,
    arity: 2,
    typeFor: () => mk(piMk("k", intMk, piMk("e", intMk, intMk))),
    reduce: (args) => {
      const k = at(args, 0);
      const e = at(args, 1);
      if (k === undefined || e === undefined || k.tag !== "IntLit") return undefined;
      return vform(formScale(formOfArg(e), k.value));
    },
  },

  // -------------------------------------------------------------------------
  // The proposition `Le`, and the bridge from `ifLe` branches to hypotheses
  // -------------------------------------------------------------------------

  /**
   * `Le a b : Type 0`, the primitive proposition. Two `Le`s are the *same proposition*
   * when `b - a` and `d - c` have the same linear form; that is what makes the `no` branch
   * of `ifLe (x + 1) lo`, whose hypothesis is `Le (lo + 1) (x + 1)`, usable where `Le lo x`
   * is expected (section 6.3).
   */
  [OP_LE]: {
    name: OP_LE,
    arity: 2,
    typeFor: () => mk(piMk("a", intMk, piMk("b", intMk, type0))),
    convArgs: (a, b) => {
      const [a0, a1] = a;
      const [b0, b1] = b;
      if (a0 === undefined || a1 === undefined || b0 === undefined || b1 === undefined) return undefined;
      return formEquals(formSub(formOfArg(a1), formOfArg(a0)), formSub(formOfArg(b1), formOfArg(b0)));
    },
  },

  /**
   * `ifLe {A : Type l} a b (yes : Le a b -> A) (no : Lt b a -> A) : A`. With literal
   * bounds it selects the branch and hands it a proof, built from `byContra` and a
   * one-hypothesis Farkas certificate; otherwise it stays stuck, so each branch of a case
   * split sees its hypothesis. The branches themselves are relevant arguments: the result
   * is a *value* of type `A`, not a proof.
   */
  [OP_IF_LE]: {
    name: OP_IF_LE,
    arity: 5,
    typeFor: (level) =>
      mk(
        piMk(
          "A",
          sortMk(level),
          piMk(
            "a",
            intMk,
            piMk(
              "b",
              intMk,
              piMk("yes", arrowOf(leOf(varMk("a"), varMk("b")), varMk("A")), piMk("no", arrowOf(ltOf(varMk("b"), varMk("a")), varMk("A")), varMk("A"))),
            ),
          ),
        ),
      ),
    reduce: (args, ctx) => {
      const a = at(args, 1);
      const b = at(args, 2);
      if (a === undefined || b === undefined || a.tag !== "IntLit" || b.tag !== "IntLit") return undefined;
      if (a.value <= b.value) {
        const yes = at(args, 3);
        return yes === undefined ? undefined : ctx.apply(yes, ctx.evalIn(leProofTerm(a.value, b.value), []));
      }
      const no = at(args, 4);
      return no === undefined ? undefined : ctx.apply(no, ctx.evalIn(leProofTerm(b.value + 1n, a.value), []));
    },
  },

  /**
   * `byContra a b (k : Lt b a -> Empty) : Le a b`. Sound because integers are totally
   * ordered: `¬(b < a)` gives `a <= b`. The refutation `k` is irrelevant: all proofs of
   * `Le a b` are interchangeable, and nothing computes with it.
   */
  [OP_BY_CONTRA]: {
    name: OP_BY_CONTRA,
    arity: 3,
    typeFor: () =>
      mk(piMk("a", intMk, piMk("b", intMk, piMk("k", notOf(ltOf(varMk("b"), varMk("a"))), leOf(varMk("a"), varMk("b")))))),
    irrelevant: [2],
  },

  /** `intEq a b (p : Le a b) (q : Le b a) : Eq Int a b`; both proofs are irrelevant. */
  [OP_INT_EQ]: {
    name: OP_INT_EQ,
    arity: 4,
    typeFor: () =>
      mk(
        piMk(
          "a",
          intMk,
          piMk(
            "b",
            intMk,
            piMk("p", leOf(varMk("a"), varMk("b")), piMk("q", leOf(varMk("b"), varMk("a")), eqMk(intMk, varMk("a"), varMk("b")))),
          ),
        ),
      ),
    irrelevant: [2, 3],
  },

  // -------------------------------------------------------------------------
  // Vectors
  // -------------------------------------------------------------------------

  /** `Vec (A : Type 0) (n : Int) : Type 0`. Lengths compare by linear form. */
  [OP_VEC]: {
    name: OP_VEC,
    arity: 2,
    typeFor: () => mk(piMk("A", type0, piMk("n", intMk, type0))),
  },

  /** `len A n v` reduces to `n`: the length is carried by the type. */
  [OP_LEN]: {
    name: OP_LEN,
    arity: 3,
    typeFor: () => mk(piMk("A", type0, piMk("n", intMk, piMk("v", vecOf(varMk("A"), varMk("n")), intMk)))),
    reduce: (args) => at(args, 1),
  },

  /**
   * `vecBounds A n v : And (Le 0 n) (Le n 4294967295)`. A primitive lemma: vectors can
   * only be built by `append`, `slice` and `castVec`, all of which enforce the bound, and
   * a vector parameter of a verified function arrives with it (section 6.3).
   */
  [OP_VEC_BOUNDS]: {
    name: OP_VEC_BOUNDS,
    arity: 3,
    typeFor: () =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "n",
            intMk,
            piMk("v", vecOf(varMk("A"), varMk("n")), andOf(leOf(intLitMk(0n), varMk("n")), leOf(varMk("n"), intLitMk(MAX_VEC_LEN)))),
          ),
        ),
      ),
  },

  /** `get A n v i p : A`, with `p : And (Le 0 i) (Lt i n)`. The bounds proof is irrelevant. */
  [OP_GET]: {
    name: OP_GET,
    arity: 5,
    typeFor: () =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "n",
            intMk,
            piMk(
              "v",
              vecOf(varMk("A"), varMk("n")),
              piMk(
                "i",
                intMk,
                piMk(
                  "p",
                  andOf(leOf(intLitMk(0n), varMk("i")), ltOf(varMk("i"), varMk("n"))),
                  varMk("A"),
                ),
              ),
            ),
          ),
        ),
      ),
    irrelevant: [4],
  },

  /** `append A n m u w p : Vec A (n + m)`, with `p : Le (n + m) 4294967295`. */
  [OP_APPEND]: {
    name: OP_APPEND,
    arity: 6,
    typeFor: () =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "n",
            intMk,
            piMk(
              "m",
              intMk,
              piMk(
                "u",
                vecOf(varMk("A"), varMk("n")),
                piMk(
                  "w",
                  vecOf(varMk("A"), varMk("m")),
                  piMk(
                    "p",
                    leOf(addOf(varMk("n"), varMk("m")), intLitMk(MAX_VEC_LEN)),
                    vecOf(varMk("A"), addOf(varMk("n"), varMk("m"))),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    irrelevant: [5],
  },

  /** `slice A n v i j p : Vec A (j - i)`, with `p : And (Le 0 i) (And (Le i j) (Le j n))`. */
  [OP_SLICE]: {
    name: OP_SLICE,
    arity: 6,
    typeFor: () =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "n",
            intMk,
            piMk(
              "v",
              vecOf(varMk("A"), varMk("n")),
              piMk(
                "i",
                intMk,
                piMk(
                  "j",
                  intMk,
                  piMk(
                    "p",
                    andOf(leOf(intLitMk(0n), varMk("i")), andOf(leOf(varMk("i"), varMk("j")), leOf(varMk("j"), varMk("n")))),
                    vecOf(varMk("A"), subOf(varMk("j"), varMk("i"))),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    irrelevant: [5],
  },

  /** `castVec A n m e v : Vec A m` for `e : Eq Int n m`; the equality proof is irrelevant. */
  [OP_CAST_VEC]: {
    name: OP_CAST_VEC,
    arity: 5,
    typeFor: () =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "n",
            intMk,
            piMk(
              "m",
              intMk,
              piMk("e", eqMk(intMk, varMk("n"), varMk("m")), piMk("v", vecOf(varMk("A"), varMk("n")), vecOf(varMk("A"), varMk("m")))),
            ),
          ),
        ),
      ),
    irrelevant: [3],
  },

  // -------------------------------------------------------------------------
  // Well-founded recursion, and division by a constant
  // -------------------------------------------------------------------------

  /**
   * `fixWf : (A : Type 0) -> (B : A -> Type l) -> (m : A -> Int)
   *        -> (step : (x : A) -> Le 0 (m x)
   *                   -> ((y : A) -> Le 0 (m y) -> Lt (m y) (m x) -> B y)
   *                   -> B x)
   *        -> (x : A) -> Le 0 (m x) -> B x`
   *
   * There is deliberately **no** `reduce`: `fixWf` is opaque, so conversion always
   * terminates and never unfolds a recursive function. Callers use the function's type.
   * The non-negativity proof is irrelevant; nothing computes with it.
   */
  [OP_FIX_WF]: {
    name: OP_FIX_WF,
    arity: 6,
    typeFor: (level) =>
      mk(
        piMk(
          "A",
          type0,
          piMk(
            "B",
            arrowOf(varMk("A"), sortMk(level)),
            piMk(
              "m",
              arrowOf(varMk("A"), intMk),
              piMk(
                "step",
                piMk(
                  "x",
                  varMk("A"),
                  piMk(
                    "px",
                    leOf(intLitMk(0n), appC(varMk("m"), varMk("x"))),
                    piMk(
                      "ih",
                      piMk(
                        "y",
                        varMk("A"),
                        piMk(
                          "py",
                          leOf(intLitMk(0n), appC(varMk("m"), varMk("y"))),
                          piMk(
                            "lt",
                            ltOf(appC(varMk("m"), varMk("y")), appC(varMk("m"), varMk("x"))),
                            appC(varMk("B"), varMk("y")),
                          ),
                        ),
                      ),
                      appC(varMk("B"), varMk("x")),
                    ),
                  ),
                ),
                piMk(
                  "x",
                  varMk("A"),
                  piMk("px", leOf(intLitMk(0n), appC(varMk("m"), varMk("x"))), appC(varMk("B"), varMk("x"))),
                ),
              ),
            ),
          ),
        ),
      ),
    irrelevant: [5],
  },

  /**
   * `divFloor e k` with `k` a positive integer literal: floor division, exact on safe
   * integers, encoded with linear bounds and never with SMT `div`. A non-literal divisor
   * is rejected by `check.ts` (`positiveLiteralArgs`), because the lemma below is only
   * true for `k > 0`.
   */
  [OP_DIV_FLOOR]: {
    name: OP_DIV_FLOOR,
    arity: 2,
    typeFor: () => mk(piMk("e", intMk, piMk("k", intMk, intMk))),
    positiveLiteralArgs: [1],
    reduce: (args) => {
      const e = at(args, 0);
      const k = at(args, 1);
      if (e === undefined || k === undefined || e.tag !== "IntLit" || k.tag !== "IntLit" || k.value <= 0n) {
        return undefined;
      }
      return vint(floorDiv(e.value, k.value));
    },
  },

  /** `divFloorSpec e k : And (Le (k*q) e) (Le e (k*q + k - 1))` where `q = divFloor e k`. */
  [OP_DIV_FLOOR_SPEC]: {
    name: OP_DIV_FLOOR_SPEC,
    arity: 2,
    typeFor: () =>
      mk(
        piMk(
          "e",
          intMk,
          piMk(
            "k",
            intMk,
            andOf(
              leOf(mulConstOf(varMk("k"), divFloorOf(varMk("e"), varMk("k"))), varMk("e")),
              leOf(varMk("e"), addOf(mulConstOf(varMk("k"), divFloorOf(varMk("e"), varMk("k"))), subOf(varMk("k"), intLitMk(1n)))),
            ),
          ),
        ),
      ),
    positiveLiteralArgs: [1],
  },

  /** `divTrunc e k` with `k` a positive literal: truncation toward zero. */
  [OP_DIV_TRUNC]: {
    name: OP_DIV_TRUNC,
    arity: 2,
    typeFor: () => mk(piMk("e", intMk, piMk("k", intMk, intMk))),
    positiveLiteralArgs: [1],
    reduce: (args) => {
      const e = at(args, 0);
      const k = at(args, 1);
      if (e === undefined || k === undefined || e.tag !== "IntLit" || k.tag !== "IntLit" || k.value <= 0n) {
        return undefined;
      }
      return vint(truncDiv(e.value, k.value));
    },
  },

  /**
   * `divTruncSpecNonneg e k (h : Le 0 e) : And (Le (k*q) e) (Le e (k*q + k - 1))` where
   * `q = divTrunc e k`. For a non-negative dividend truncation is floor division.
   */
  [OP_DIV_TRUNC_SPEC_NONNEG]: {
    name: OP_DIV_TRUNC_SPEC_NONNEG,
    arity: 3,
    typeFor: () =>
      mk(
        piMk(
          "e",
          intMk,
          piMk(
            "k",
            intMk,
            piMk(
              "h",
              leOf(intLitMk(0n), varMk("e")),
              andOf(
                leOf(mulConstOf(varMk("k"), divTruncOf(varMk("e"), varMk("k"))), varMk("e")),
                leOf(varMk("e"), addOf(mulConstOf(varMk("k"), divTruncOf(varMk("e"), varMk("k"))), subOf(varMk("k"), intLitMk(1n)))),
              ),
            ),
          ),
        ),
      ),
    irrelevant: [2],
    positiveLiteralArgs: [1],
  },

  /**
   * `divTruncSpecNeg e k (h : Lt e 0) : And (Le (k*q - k + 1) e) (Le e (k*q))` where
   * `q = divTrunc e k`. For a negative dividend, truncation rounds up.
   */
  [OP_DIV_TRUNC_SPEC_NEG]: {
    name: OP_DIV_TRUNC_SPEC_NEG,
    arity: 3,
    typeFor: () =>
      mk(
        piMk(
          "e",
          intMk,
          piMk(
            "k",
            intMk,
            piMk(
              "h",
              ltOf(varMk("e"), intLitMk(0n)),
              andOf(
                leOf(addOf(subOf(mulConstOf(varMk("k"), divTruncOf(varMk("e"), varMk("k"))), varMk("k")), intLitMk(1n)), varMk("e")),
                leOf(varMk("e"), mulConstOf(varMk("k"), divTruncOf(varMk("e"), varMk("k")))),
              ),
            ),
          ),
        ),
      ),
    irrelevant: [2],
    positiveLiteralArgs: [1],
  },
});

/** The info for an op tag, or `undefined` when the tag is not a built-in. */
export function lookupPrim(op: PrimOp): PrimInfo | undefined {
  if (!Object.hasOwn(PRIMS, op)) return undefined;
  const info: PrimInfo | undefined = PRIMS[op];
  return info;
}

// ---------------------------------------------------------------------------
// Generated proof terms
// ---------------------------------------------------------------------------

/**
 * `byContra x y (fun (k : Lt y x) => Farkas [k] [1]) : Le x y`.
 *
 * A proof of `Le x y` for literal `x <= y` needs no new primitive: assuming `Lt y x`
 * gives the row `x - y - 1 < 0`, so a one-hypothesis certificate refutes it. `ifLe` uses
 * this to hand each branch exactly the hypothesis it expects, and the same construction
 * is available to the elaborator.
 */
export function leProofTerm(x: bigint, y: bigint): Term {
  return primTerm(OP_BY_CONTRA, [
    intLit(x),
    intLit(y),
    mk(lamMk("k", leOf(intLitMk(y + 1n), intLitMk(x)), farkasMk([varMk("k")], [1n]))),
  ]);
}

// ---------------------------------------------------------------------------
// Prelude definitions
// ---------------------------------------------------------------------------

const AND_TYPE: Term = mk(piMk("A", type0, piMk("B", type0, type0)));

/** `And = fun A B => Sigma (_ : A). B` — the non-dependent Sigma. */
const AND_VALUE: Term = mk(lamMk("A", type0, lamMk("B", type0, sigmaMk("_", varMk("A"), varMk("B")))));

const NOT_TYPE: Term = mk(piMk("A", type0, type0));

/** `Not = fun A => A -> Empty`. */
const NOT_VALUE: Term = mk(lamMk("A", type0, piMk("_", varMk("A"), emptyMk)));

const LT_TYPE: Term = mk(piMk("a", intMk, piMk("b", intMk, type0)));

/** `Lt = fun a b => Le (a + 1) b`: strict inequality for integers. */
const LT_VALUE: Term = mk(
  lamMk("a", intMk, lamMk("b", intMk, leOf(addOf(varMk("a"), intLitMk(1n)), varMk("b")))),
);

const IN_RANGE_TYPE: Term = mk(piMk("x", intMk, type0));

/** `InRange = fun x => And (Le (-(2^53-1)) x) (Le x (2^53-1))`. */
const IN_RANGE_VALUE: Term = mk(
  lamMk(
    "x",
    intMk,
    andOf(
      leOf(negOf(intLitMk(SAFE_MAX)), varMk("x")),
      leOf(varMk("x"), intLitMk(SAFE_MAX)),
    ),
  ),
);

/**
 * The prelude: definitions only, never axioms. `emptyEnv()` inserts each of these through
 * `addDecl`, so the kernel type-checks its own prelude.
 */
export function builtinDecls(): Decl[] {
  return [
    { kind: "def", name: AND_NAME, type: AND_TYPE, value: AND_VALUE },
    { kind: "def", name: NOT_NAME, type: NOT_TYPE, value: NOT_VALUE },
    { kind: "def", name: LT_NAME, type: LT_TYPE, value: LT_VALUE },
    { kind: "def", name: IN_RANGE_NAME, type: IN_RANGE_TYPE, value: IN_RANGE_VALUE },
  ];
}
