/**
 * Unit tests for the erased-term interpreter (milestone 9).
 *
 * The terms here are built by hand (with the kernel's own constructors, so the de Bruijn
 * indices are right) and then erased, which is exactly what the differential driver feeds
 * the interpreter.  The tests pin the interpretation rules: `fixWf` is real recursion,
 * vectors are JS arrays, `Sum`/`Sigma` are tagged objects, arithmetic runs on bigints and
 * `ifLe` picks a branch — and proof positions are never forced.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import {
  DEFAULT_MAX_STEPS,
  GlobalTable,
  InterpBudgetError,
  decodeSum,
  encodeSum,
  inl,
  inr,
  interpTerm,
  isPair,
  isSum,
  isVector,
  lambdaArity,
  pair,
  projectPath,
  proof,
  showValue,
  type IrValue,
} from "../../src/difftest/interp";

/** Interpret a closed (or lambda) kernel term, erasing it first, and apply the arguments. */
function run(term: K.Term, args: readonly IrValue[] = [], globals?: GlobalTable): IrValue {
  return interpTerm(K.erase(term), globals === undefined ? {} : { globals })(args);
}

const V = (index: number): K.Term => K.varTerm(index);

describe("arithmetic", () => {
  test("add, sub, neg and mulConst run on bigints", () => {
    expect(run(K.Add(K.intLit(2n), K.intLit(3n)))).toBe(5n);
    expect(run(K.Sub(K.intLit(2n), K.intLit(5n)))).toBe(-3n);
    expect(run(K.Neg(K.intLit(7n)))).toBe(-7n);
    expect(run(K.MulConst(K.intLit(3n), K.intLit(4n)))).toBe(12n);
  });

  test("divFloor and divTrunc round the way their names say", () => {
    expect(run(K.DivFloor(K.intLit(-7n), K.intLit(2n)))).toBe(-4n);
    expect(run(K.DivFloor(K.intLit(7n), K.intLit(2n)))).toBe(3n);
    expect(run(K.DivTrunc(K.intLit(-7n), K.intLit(2n)))).toBe(-3n);
    expect(run(K.DivTrunc(K.intLit(7n), K.intLit(2n)))).toBe(3n);
  });

  test("arithmetic on a non-number is the proof placeholder, never a throw", () => {
    expect(run(K.Add(K.intLit(1n), K.tt))).toBe(proof);
    expect(run(K.app(K.intLit(1n), K.intLit(2n)))).toBe(proof);
  });
});

describe("ifLe", () => {
  const branch = (a: bigint, b: bigint): K.Term =>
    K.IfLe(
      0,
      K.Int,
      K.intLit(a),
      K.intLit(b),
      K.lam("h", K.Unit, K.intLit(10n)),
      K.lam("h", K.Unit, K.intLit(20n)),
    );

  test("picks the yes branch when a <= b and the no branch otherwise", () => {
    expect(run(branch(1n, 2n))).toBe(10n);
    expect(run(branch(2n, 2n))).toBe(10n);
    expect(run(branch(3n, 2n))).toBe(20n);
  });

  test("the branch receives the proof placeholder and can ignore it", () => {
    // `yes` returns its argument: the interpreter hands it the placeholder.
    const term = K.IfLe(
      0,
      K.Int,
      K.intLit(0n),
      K.intLit(1n),
      K.lam("h", K.Unit, K.varTerm(0)),
      K.lam("h", K.Unit, K.intLit(9n)),
    );
    expect(run(term)).toBe(proof);
  });
});

describe("vectors are JS arrays", () => {
  const vec2 = (): readonly IrValue[] => [10n, 20n];

  test("len is the length the type carries", () => {
    const term = K.mk(
      K.lamMk(
        "v",
        K.primMk(K.OP_VEC, [K.primMk(K.OP_INT, []), K.intLitMk(2n)]),
        K.primMk(K.OP_LEN, [K.primMk(K.OP_INT, []), K.intLitMk(2n), K.varMk("v")]),
      ),
    );
    expect(run(term, [vec2()])).toBe(2n);
  });

  test("get reads the element at the index", () => {
    const vectorType = K.primMk(K.OP_VEC, [K.primMk(K.OP_INT, []), K.intLitMk(2n)]);
    const term = K.mk(
      K.lamMk(
        "v",
        vectorType,
        K.primMk(K.OP_GET, [K.primMk(K.OP_INT, []), K.intLitMk(2n), K.varMk("v"), K.intLitMk(1n), K.primMk(K.OP_TT, [])]),
      ),
    );
    expect(run(term, [vec2()])).toBe(20n);
    // Out of bounds is the placeholder, not an exception.
    const outOfBounds = K.mk(
      K.lamMk(
        "v",
        vectorType,
        K.primMk(K.OP_GET, [K.primMk(K.OP_INT, []), K.intLitMk(2n), K.varMk("v"), K.intLitMk(7n), K.primMk(K.OP_TT, [])]),
      ),
    );
    expect(run(outOfBounds, [vec2()])).toBe(proof);
  });

  test("append concatenates and slice cuts", () => {
    const append = K.mk(
      K.lamMk(
        "u",
        K.primMk(K.OP_VEC, [K.primMk(K.OP_INT, []), K.intLitMk(2n)]),
        K.lamMk(
          "w",
          K.primMk(K.OP_VEC, [K.primMk(K.OP_INT, []), K.intLitMk(1n)]),
          K.primMk(K.OP_APPEND, [
            K.primMk(K.OP_INT, []),
            K.intLitMk(2n),
            K.intLitMk(1n),
            K.varMk("u"),
            K.varMk("w"),
            K.primMk(K.OP_TT, []),
          ]),
        ),
      ),
    );
    expect(run(append, [[10n, 20n], [30n]])).toEqual([10n, 20n, 30n]);

    const slice = K.mk(
      K.lamMk(
        "v",
        K.primMk(K.OP_VEC, [K.primMk(K.OP_INT, []), K.intLitMk(4n)]),
        K.primMk(K.OP_SLICE, [
          K.primMk(K.OP_INT, []),
          K.intLitMk(4n),
          K.varMk("v"),
          K.intLitMk(1n),
          K.intLitMk(3n),
          K.primMk(K.OP_TT, []),
        ]),
      ),
    );
    expect(run(slice, [[10n, 20n, 30n, 40n]])).toEqual([20n, 30n]);
  });

  test("isVector recognizes interpreted arrays", () => {
    expect(isVector([1n])).toBe(true);
    expect(isVector(1n)).toBe(false);
    expect(isVector(pair(1n, 2n))).toBe(false);
  });
});

describe("Sum and Sigma encodings", () => {
  test("inl/inr are tagged objects and case dispatches on the tag", () => {
    expect(isSum(inl(1n))).toBe(true);
    expect(showValue(inl(1n))).toBe("inl(1)");
    expect(showValue(inr(pair(1n, 2n)))).toBe("inr(⟨1, 2⟩)");

    const caseTerm = (scrutinee: K.Term): K.Term =>
      K.SumCase(
        0,
        K.Int,
        K.Int,
        K.lam("s", K.Sum(K.Int, K.Int), K.Int),
        K.lam("a", K.Int, K.intLit(100n)),
        K.lam("b", K.Int, K.intLit(200n)),
        scrutinee,
      );
    expect(run(caseTerm(K.Inl(K.Int, K.Int, K.intLit(1n))))).toBe(100n);
    expect(run(caseTerm(K.Inr(K.Int, K.Int, K.intLit(1n))))).toBe(200n);
    // A scrutinee that is not an injection: the placeholder, not a throw.
    expect(run(caseTerm(K.intLit(3n)))).toBe(proof);
  });

  test("pair/fst/snd and projectPath", () => {
    const sigma = K.sigma("a", K.Int, K.Int);
    const value = K.pair(sigma, K.intLit(1n), K.intLit(2n));
    expect(run(K.fst(value))).toBe(1n);
    expect(run(K.snd(value))).toBe(2n);
    expect(isPair(run(value))).toBe(true);
    const nested = pair(1n, pair(2n, 3n));
    expect(projectPath(nested, [0])).toBe(1n);
    expect(projectPath(nested, [1, 0])).toBe(2n);
    expect(projectPath(nested, [1, 1])).toBe(3n);
    // Projecting a non-pair is the placeholder.
    expect(projectPath(1n, [0])).toBe(proof);
  });

  test("encodeSum/decodeSum agree with the extractor's right-nested Sum", () => {
    for (const count of [1, 2, 3]) {
      for (let index = 0; index < count; index += 1) {
        const record = pair(BigInt(index), proof);
        const encoded = encodeSum(index, count, record);
        expect(decodeSum(encoded, count)).toEqual({ index, payload: record });
      }
    }
    // Two variants, as every accepted union has: `inl` and `inr` of the record.
    expect(encodeSum(0, 2, 7n)).toEqual(inl(7n));
    expect(encodeSum(1, 2, 7n)).toEqual(inr(7n));
    expect(decodeSum(inl(7n), 2)).toEqual({ index: 0, payload: 7n });
    expect(decodeSum(inr(7n), 2)).toEqual({ index: 1, payload: 7n });
    expect(decodeSum(7n, 2)).toBeUndefined();
  });
});

describe("fixWf is real recursion", () => {
  /**
   * `fun n => fixWf … step n tt` where
   * `step = fun x px ih => ifLe x 0 (0) (x + ih (x - 1) tt tt)` — the sum `x + (x-1) + …`.
   */
  const sumDown: K.Term = K.mk(
    K.lamMk(
      "n",
      K.primMk(K.OP_INT, []),
      K.primMk(
        K.OP_FIX_WF,
        [
          K.sortMk(0),
          K.sortMk(0),
          K.lamMk("_", K.primMk(K.OP_INT, []), K.varMk("_")),
          K.lamMk(
            "x",
            K.primMk(K.OP_INT, []),
            K.lamMk(
              "px",
              K.primMk(K.OP_UNIT, []),
              K.lamMk(
                "ih",
                K.primMk(K.OP_UNIT, []),
                K.primMk(
                  K.OP_IF_LE,
                  [
                    K.sortMk(0),
                    K.varMk("x"),
                    K.intLitMk(0n),
                    K.lamMk("h", K.primMk(K.OP_UNIT, []), K.intLitMk(0n)),
                    K.lamMk(
                      "h",
                      K.primMk(K.OP_UNIT, []),
                      K.primMk(K.OP_ADD, [
                        K.varMk("x"),
                        K.appManyMk(K.varMk("ih"), [
                          K.primMk(K.OP_SUB, [K.varMk("x"), K.intLitMk(1n)]),
                          K.intLitMk(0n),
                          K.intLitMk(0n),
                        ]),
                      ]),
                    ),
                  ],
                  0,
                ),
              ),
            ),
          ),
          K.varMk("n"),
          K.intLitMk(0n),
        ],
        0,
      ),
    ),
  );

  test("the induction hypothesis recurses", () => {
    const interpret = interpTerm(K.erase(sumDown));
    expect(interpret([0n])).toBe(0n);
    expect(interpret([1n])).toBe(1n);
    expect(interpret([5n])).toBe(15n);
    expect(interpret([100n])).toBe(5050n);
  });

  test("the evaluation budget stops a runaway term instead of hanging", () => {
    const interpret = interpTerm(K.erase(sumDown), { maxSteps: 200 });
    expect(() => interpret([1000n])).toThrow(InterpBudgetError);
    // A fresh call gets a fresh budget, and the default is generous.
    expect(interpret([3n])).toBe(6n);
    expect(DEFAULT_MAX_STEPS).toBeGreaterThan(100_000);
  });
});

describe("proof positions are irrelevant", () => {
  test("a proof argument is never evaluated, so nonsense in it cannot matter", () => {
    // `get`'s bounds proof and `absurd`'s proof are irrelevant positions: the term below
    // contains an ill-formed application there and still returns the element.
    const term = K.mk(
      K.lamMk(
        "v",
        K.primMk(K.OP_VEC, [K.primMk(K.OP_INT, []), K.intLitMk(1n)]),
        K.primMk(K.OP_GET, [
          K.primMk(K.OP_INT, []),
          K.intLitMk(1n),
          K.varMk("v"),
          K.intLitMk(0n),
          K.appMk(K.intLitMk(9n), K.intLitMk(9n)),
        ]),
      ),
    );
    expect(run(term, [[42n]])).toBe(42n);
  });

  test("`Const` of an unknown name and `Erased` are placeholders", () => {
    expect(run(K.constTerm("nowhere"))).toBe(proof);
    expect(run(K.sort(0))).toBe(proof);
  });
});

describe("globals", () => {
  test("a defined name is interpreted, an undefined one is the placeholder", () => {
    const globals = new GlobalTable([["inc", K.lam("x", K.Int, K.Add(K.varTerm(0), K.intLit(1n)))]]);
    expect(run(K.app(K.constTerm("inc"), K.intLit(41n)), [], globals)).toBe(42n);
    expect(run(K.constTerm("missing"), [], globals)).toBe(proof);
  });

  test("a recursive Const does not loop forever", () => {
    const globals = new GlobalTable();
    globals.define("loop", K.constTerm("loop"));
    expect(run(K.constTerm("loop"), [], globals)).toBe(proof);
  });
});

describe("the term's shape", () => {
  test("lambdaArity counts the leading lambdas", () => {
    expect(lambdaArity(K.erase(K.lam("a", K.Int, K.lam("b", K.Int, K.intLit(1n)))))).toBe(2);
    expect(lambdaArity(K.erase(K.intLit(1n)))).toBe(0);
  });

  test("showValue renders the encodings readably", () => {
    expect(showValue(5n)).toBe("5");
    expect(showValue([1n, 2n])).toBe("[1, 2]");
    expect(showValue(pair(1n, 2n))).toBe("⟨1, 2⟩");
    expect(showValue(proof)).toBe("<proof>");
  });
});
