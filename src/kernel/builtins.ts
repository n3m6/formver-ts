/**
 * Built-in ops: their types, reduction rules, conversion rules and the prelude
 * definitions seeded into `emptyEnv()`.
 *
 * The logic built-ins of specification section 6.1.3 are here:
 *
 *   Empty, Unit, tt, Sum (inl, inr, dependent case), absurd, Eq (refl, J)
 *
 * `And` and `Not` are *definitions*, not ops: `And A B` is the non-dependent `Sigma` and
 * `Not A` is `A -> Empty`, so they need no primitive rule. They are inserted through
 * `addDecl` by `emptyEnv()`, which is the only insertion path and type-checks them.
 *
 * Milestone 3 completes `Int` and `Le` and adds `Lt`, `ifLe`, `byContra`, `intEq`,
 * `InRange`, `Vec`, `len`, `vecBounds`, `get`, `append`, `slice`, `castVec`, `fixWf`,
 * `divFloor` and `divTrunc` *by adding entries to `PRIMS`* (and two more definitions to
 * `builtinDecls`). Nothing in `eval.ts`, `check.ts` or `conv.ts` needs to change:
 *
 *   - a new op needs `name`, `arity`, `typeFor`, and optionally `reduce`
 *     (no `reduce` means opaque, which is exactly how `fixWf` stays non-unfolding);
 *   - `irrelevant` marks proof arguments ignored by conversion and by atom keys;
 *   - `convArgs` overrides argument comparison, for `Le` (compare the linear normal forms
 *     of `b - a` and `d - c`) and `Vec` (compare lengths after linear normalization).
 */
import type { Mk, PrimOp, Term } from "./term";
import { appMk, lamMk, mk, piMk, primMk, sigmaMk, sortMk, varMk } from "./term";
import type { Decl } from "./env";
import type { PrimInfo, Value } from "./value";
import { constructorHead } from "./value";

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
/** Milestone 3: `Int` gains its operations and linear normal forms. */
export const OP_INT: PrimOp = "Int";
/** Milestone 3: `Le` gains its `convArgs` rule over linear normal forms. */
export const OP_LE: PrimOp = "Le";
/** Milestone 3: `Vec (A : Type 0) (n : Int) : Type 0`, with `len`/`get`/`append`/... */
export const OP_VEC: PrimOp = "Vec";

/** Names of the prelude *definitions* (specification section 6.1.3). */
export const AND_NAME = "And";
export const NOT_NAME = "Not";
/** Milestone 3 defines `InRange x` as `And (Le (-(2^53-1)) x) (Le x (2^53-1))`. */
export const IN_RANGE_NAME = "InRange";

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

/** Bounds-checked index into a rule's argument list; rules must tolerate a short list. */
function at(args: readonly Value[], index: number): Value | undefined {
  return index < args.length ? args[index] : undefined;
}

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
  // Milestone 3 placeholders
  // -------------------------------------------------------------------------

  /**
   * `Int : Type 0`. Milestone 2 only needs the type former, so that `IntLit` is typeable
   * and `Le` has a domain. Milestone 3 adds the operations `add`, `sub`, `neg` and
   * `mulConst`, their linear normal forms and their conversion rule.
   */
  [OP_INT]: {
    name: OP_INT,
    arity: 0,
    typeFor: () => mk(type0),
  },

  /**
   * `Le a b : Type 0`, the primitive proposition. Milestone 2 types it and converts it
   * structurally. That is sound but incomplete: `Le a b` and `Le c d` whose differences
   * have the same linear normal form are not yet identified. Milestone 3 adds
   * `convArgs: (a, b) => <linear normal forms of b[1] - b[0] and a[1] - a[0] agree>`.
   */
  [OP_LE]: {
    name: OP_LE,
    arity: 2,
    typeFor: () => mk(piMk("a", intMk, piMk("b", intMk, type0))),
  },
});

/** The info for an op tag, or `undefined` when the tag is not a built-in. */
export function lookupPrim(op: PrimOp): PrimInfo | undefined {
  if (!Object.hasOwn(PRIMS, op)) return undefined;
  const info: PrimInfo | undefined = PRIMS[op];
  return info;
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

/**
 * The prelude: definitions only, never axioms. `emptyEnv()` inserts each of these through
 * `addDecl`, so the kernel type-checks its own prelude.
 *
 * Milestone 3 appends `Lt := fun a b => Le (add a 1) b` and
 * `InRange := fun x => And (Le (neg 9007199254740991) x) (Le x 9007199254740991)`.
 */
export function builtinDecls(): Decl[] {
  return [
    { kind: "def", name: AND_NAME, type: AND_TYPE, value: AND_VALUE },
    { kind: "def", name: NOT_NAME, type: NOT_TYPE, value: NOT_VALUE },
  ];
}
