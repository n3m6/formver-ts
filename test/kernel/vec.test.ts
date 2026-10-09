/**
 * Milestone 3: vectors (`Vec`, `len`, `vecBounds`, `get`, `append`, `slice`, `castVec`)
 * and the opaque well-founded recursion combinator `fixWf`.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { expectErr } from "./helpers";
import {
  addMk,
  andMk,
  appendMk,
  boundsProof,
  castVecMk,
  conv,
  env,
  getMk,
  intMk,
  leMk,
  leProofMk,
  eqMk,
  lenMk,
  ltMk,
  mulConstMk,
  norm,
  show,
  showType,
  sliceMk,
  subMk,
  v,
  vecBoundsMk,
  vecMk,
} from "./helpers3";

const lit = K.intLit;

describe("Vec and len", () => {
  test("Vec (A : Type 0) (n : Int) : Type 0", () => {
    expect(showType(K.Vec(K.Int, lit(3)))).toBe("Type 0");
    expect(showType(K.Vec(K.Unit, K.Add(lit(1), lit(1))))).toBe("Type 0");
    expect(K.inferType(env, K.Vec(K.Unit, K.tt)).ok).toBe(false);
  });

  test("Vec A (n + 0) is Vec A n, but Vec A (n + 1) and 2 * n are not", () => {
    const shifted = K.mk(K.lamMk("n", intMk, vecMk(intMk, addMk(v("n"), K.intLitMk(0n)))));
    const plain = K.mk(K.lamMk("n", intMk, vecMk(intMk, v("n"))));
    const next = K.mk(K.lamMk("n", intMk, vecMk(intMk, addMk(v("n"), K.intLitMk(1n)))));
    const twice = K.mk(K.lamMk("n", intMk, vecMk(intMk, mulConstMk(2n, v("n")))));
    const otherElt = K.mk(K.lamMk("n", intMk, vecMk(() => K.Unit, v("n"))));
    expect(conv(shifted, plain)).toBe(true);
    expect(conv(next, plain)).toBe(false);
    expect(conv(twice, plain)).toBe(false);
    expect(conv(plain, otherElt)).toBe(false);
  });

  test("len A n v reduces to n, even when the length is a linear expression", () => {
    const term = K.mk(K.lamMk("n", intMk, K.lamMk("w", vecMk(intMk, v("n")), lenMk(intMk, v("n"), v("w")))));
    const expected = K.mk(K.lamMk("n", intMk, K.lamMk("w", vecMk(intMk, v("n")), v("n"))));
    expect(conv(term, expected)).toBe(true);
    expect(showType(term)).toBe("((n : Int()) -> ((w : Vec(Int(), n)) -> Int()))");
    const shifted = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk("w", vecMk(intMk, addMk(v("n"), K.intLitMk(0n))), lenMk(intMk, addMk(v("n"), K.intLitMk(0n)), v("w"))),
      ),
    );
    expect(conv(shifted, expected)).toBe(true);
  });

  test("vecBounds A n v : And (Le 0 n) (Le n 4294967295)", () => {
    const term = K.mk(K.lamMk("n", intMk, K.lamMk("w", vecMk(intMk, v("n")), vecBoundsMk(intMk, v("n"), v("w")))));
    const type = K.mk(
      K.piMk(
        "n",
        intMk,
        K.piMk(
          "w",
          vecMk(intMk, v("n")),
          andMk(leMk(K.intLitMk(0n), v("n")), leMk(v("n"), K.intLitMk(4294967295n))),
        ),
      ),
    );
    expect(K.checkType(env, term, type).ok).toBe(true);
  });
});

describe("get", () => {
  test("get A n v i p : A, with the bounds proof as an argument", () => {
    const term = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(1n), () => boundsProof(1n, 3n)),
      ),
    );
    expect(showType(term)).toBe("((w : Vec(Int(), 3)) -> Int())");
  });

  test("the bounds proof is irrelevant: a different proof of the same fact is accepted", () => {
    const withHelper = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(1n), () => boundsProof(1n, 3n)),
      ),
    );
    const handBuilt = K.mk(
      K.lamMk(
        "w",
        vecMk(intMk, K.intLitMk(3n)),
        getMk(intMk, K.intLitMk(3n), v("w"), K.intLitMk(1n), () =>
          K.pair(K.And(K.Le(lit(0), lit(1)), K.Lt(lit(1), lit(3))), K.LeProof(0n, 1n), K.LeProof(2n, 3n)),
        ),
      ),
    );
    expect(K.inferType(env, handBuilt).ok).toBe(true);
    expect(conv(withHelper, handBuilt)).toBe(true);
  });

  test("get atoms are keyed by the length expression, not by its syntax", () => {
    const boundsOf = (n: K.Mk): K.Mk => andMk(leMk(K.intLitMk(0n), v("i")), ltMk(v("i"), n));
    const left = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "w",
          vecMk(intMk, v("n")),
          K.lamMk("i", intMk, K.lamMk("p", boundsOf(v("n")), getMk(intMk, v("n"), v("w"), v("i"), v("p")))),
        ),
      ),
    );
    const sameLengthAsSum = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "w",
          vecMk(intMk, v("n")),
          K.lamMk(
            "i",
            intMk,
            K.lamMk(
              "p",
              boundsOf(addMk(v("n"), K.intLitMk(0n))),
              getMk(intMk, addMk(v("n"), K.intLitMk(0n)), v("w"), v("i"), v("p")),
            ),
          ),
        ),
      ),
    );
    const otherLength = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "w",
          vecMk(intMk, v("n")),
          K.lamMk(
            "i",
            intMk,
            K.lamMk(
              "p",
              boundsOf(addMk(v("n"), K.intLitMk(1n))),
              getMk(intMk, addMk(v("n"), K.intLitMk(1n)), v("w"), v("i"), v("p")),
            ),
          ),
        ),
      ),
    );
    expect(K.inferType(env, sameLengthAsSum).ok).toBe(true);
    expect(conv(left, sameLengthAsSum)).toBe(true);
    expect(conv(left, otherLength)).toBe(false);
  });
});

describe("append, slice and castVec", () => {
  const appendType = K.mk(
    K.piMk(
      "n",
      intMk,
      K.piMk(
        "m",
        intMk,
        K.piMk(
          "u",
          vecMk(intMk, v("n")),
          K.piMk(
            "w",
            vecMk(intMk, v("m")),
            K.piMk(
              "p",
              leMk(addMk(v("n"), v("m")), K.intLitMk(4294967295n)),
              vecMk(intMk, addMk(v("n"), v("m"))),
            ),
          ),
        ),
      ),
    ),
  );

  const appendTerm = K.mk(
    K.lamMk(
      "n",
      intMk,
      K.lamMk(
        "m",
        intMk,
        K.lamMk(
          "u",
          vecMk(intMk, v("n")),
          K.lamMk(
            "w",
            vecMk(intMk, v("m")),
            K.lamMk(
              "p",
              leMk(addMk(v("n"), v("m")), K.intLitMk(4294967295n)),
              appendMk(intMk, v("n"), v("m"), v("u"), v("w"), v("p")),
            ),
          ),
        ),
      ),
    ),
  );

  test("append has the result type Vec A (n + m)", () => {
    expect(K.checkType(env, appendTerm, appendType).ok).toBe(true);
    // The same type with the length written as `0 + n + m` is still the same type.
    const withOtherSum = K.mk(
      K.piMk(
        "n",
        intMk,
        K.piMk(
          "m",
          intMk,
          K.piMk(
            "u",
            vecMk(intMk, v("n")),
            K.piMk(
              "w",
              vecMk(intMk, v("m")),
              K.piMk(
                "p",
                leMk(addMk(v("n"), v("m")), K.intLitMk(4294967295n)),
                vecMk(intMk, addMk(addMk(K.intLitMk(0n), v("n")), v("m"))),
              ),
            ),
          ),
        ),
      ),
    );
    expect(K.checkType(env, appendTerm, withOtherSum).ok).toBe(true);
  });

  test("slice A n v i j p : Vec A (j - i)", () => {
    const sliceType = K.mk(
      K.piMk(
        "n",
        intMk,
        K.piMk(
          "w",
          vecMk(intMk, v("n")),
          K.piMk(
            "i",
            intMk,
            K.piMk(
              "j",
              intMk,
              K.piMk(
                "p",
                andMk(leMk(K.intLitMk(0n), v("i")), andMk(leMk(v("i"), v("j")), leMk(v("j"), v("n")))),
                vecMk(intMk, subMk(v("j"), v("i"))),
              ),
            ),
          ),
        ),
      ),
    );
    const sliceTerm = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "w",
          vecMk(intMk, v("n")),
          K.lamMk(
            "i",
            intMk,
            K.lamMk(
              "j",
              intMk,
              K.lamMk(
                "p",
                andMk(leMk(K.intLitMk(0n), v("i")), andMk(leMk(v("i"), v("j")), leMk(v("j"), v("n")))),
                sliceMk(intMk, v("n"), v("w"), v("i"), v("j"), v("p")),
              ),
            ),
          ),
        ),
      ),
    );
    expect(K.checkType(env, sliceTerm, sliceType).ok).toBe(true);
  });

  test("castVec A n m e v : Vec A m, and it does not change the length", () => {
    const castType = K.mk(
      K.piMk(
        "n",
        intMk,
        K.piMk(
          "m",
          intMk,
          K.piMk("w", vecMk(intMk, v("n")), K.piMk("e", eqMk(intMk, v("n"), v("m")), vecMk(intMk, v("m")))),
        ),
      ),
    );
    const castTerm = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "m",
          intMk,
          K.lamMk(
            "w",
            vecMk(intMk, v("n")),
            K.lamMk("e", eqMk(intMk, v("n"), v("m")), castVecMk(intMk, v("n"), v("m"), v("e"), v("w"))),
          ),
        ),
      ),
    );
    expect(K.checkType(env, castTerm, castType).ok).toBe(true);
    // A vector of length n is also a vector of length n + 0.
    const identity = K.mk(K.lamMk("n", intMk, K.lamMk("w", vecMk(intMk, v("n")), v("w"))));
    const atShifted = K.mk(
      K.piMk("n", intMk, K.piMk("w", vecMk(intMk, v("n")), vecMk(intMk, addMk(v("n"), K.intLitMk(0n))))),
    );
    expect(K.checkType(env, identity, atShifted).ok).toBe(true);
  });

  test("intEq plus castVec moves a vector along an integer equality", () => {
    // fun (w : Vec Int (n + 0)) => castVec Int (n + 0) n (intEq ...) w
    const byContra = (a: bigint, b: bigint): K.Mk =>
      K.primMk(K.OP_BY_CONTRA, [
        K.intLitMk(a),
        K.intLitMk(b),
        K.lamMk("k", ltMk(K.intLitMk(b), K.intLitMk(a)), K.farkasMk([v("k")], [1n])),
      ]);
    const term = K.mk(
      K.lamMk(
        "n",
        intMk,
        K.lamMk(
          "w",
          vecMk(intMk, addMk(v("n"), K.intLitMk(0n))),
          castVecMk(
            intMk,
            addMk(v("n"), K.intLitMk(0n)),
            v("n"),
            K.primMk(K.OP_INT_EQ, [
              addMk(v("n"), K.intLitMk(0n)),
              v("n"),
              K.primMk(K.OP_BY_CONTRA, [
                addMk(v("n"), K.intLitMk(0n)),
                v("n"),
                K.lamMk("k", ltMk(v("n"), addMk(v("n"), K.intLitMk(0n))), K.farkasMk([v("k")], [1n])),
              ]),
              byContra(0n, 0n),
            ]),
            v("w"),
          ),
        ),
      ),
    );
    // The argument's type prints as `Vec Int n` and the result as `Vec Int n`: quoting a
    // linear value whose form is a single atom with coefficient 1 is that atom.
    expect(showType(term)).toBe("((n : Int()) -> ((w : Vec(Int(), n)) -> Vec(Int(), n)))");
  });
});

describe("fixWf", () => {
  const motive = (): K.Mk => K.lamMk("_", intMk, intMk);
  const measure = (): K.Mk => K.lamMk("_", intMk, K.intLitMk(0n));
  const step: K.Mk = K.lamMk(
    "x",
    intMk,
    K.lamMk(
      "px",
      leMk(K.intLitMk(0n), K.intLitMk(0n)),
      K.lamMk(
        "ih",
        K.piMk(
          "y",
          intMk,
          K.piMk(
            "py",
            leMk(K.intLitMk(0n), K.intLitMk(0n)),
            K.piMk("d", ltMk(K.intLitMk(0n), K.intLitMk(0n)), intMk),
          ),
        ),
        K.intLitMk(0n),
      ),
    ),
  );

  /** `fixWf Int (fun _ => Int) (fun _ => 0) step 5 proof : Int`. */
  const applied = (measureTerm: K.Mk, x: K.Mk, proof: K.Mk): K.Term =>
    K.mk(K.primMk(K.OP_FIX_WF, [intMk, motive(), measureTerm, step, x, proof], 0));

  test("fixWf is a six-argument op, and the unapplied op is not a term", () => {
    expect(K.lookupPrim(K.OP_FIX_WF)?.arity).toBe(6);
    const partial = K.mk(K.primMk(K.OP_FIX_WF, [intMk, motive(), measure(), step], 0));
    expect(expectErr(K.inferType(env, partial)).reason).toBe("prim-arity");
  });

  test("a saturated application has the motive's type", () => {
    const term = applied(measure(), K.intLitMk(5n), leProofMk(0n, 0n));
    expect(K.checkType(env, term, K.Int).ok).toBe(true);
    expect(K.checkType(env, term, K.Unit).ok).toBe(false);
  });

  test("it is opaque: the application never unfolds and never computes", () => {
    const term = applied(measure(), K.intLitMk(5n), leProofMk(0n, 0n));
    expect(show(norm(term))).toContain("fixWf");
    expect(conv(term, lit(0))).toBe(false);
    expect(conv(term, lit(5))).toBe(false);
    expect(conv(term, term)).toBe(true);
  });

  test("conversion of two fixWf applications terminates, and depends on the arguments", () => {
    const five = applied(measure(), K.intLitMk(5n), leProofMk(0n, 0n));
    const fiveAgain = applied(measure(), K.intLitMk(5n), leProofMk(0n, 0n));
    const six = applied(measure(), K.intLitMk(6n), leProofMk(0n, 0n));
    const otherMeasure = applied(K.lamMk("_", intMk, K.intLitMk(1n)), K.intLitMk(5n), leProofMk(0n, 0n));
    expect(conv(five, fiveAgain)).toBe(true);
    expect(conv(five, six)).toBe(false);
    expect(conv(five, otherMeasure)).toBe(false);
  });

  test("a step may use the induction hypothesis, which is what makes recursion work", () => {
    // step = fun x px ih =>
    //          ifLe Int 1 x
    //            (fun (h : Le 1 x) => ih (x - 1) h (leRefl x))
    //            (fun (_ : Lt x 1) => 0)
    // `h : Le 1 x` is accepted where `Le 0 (x - 1)` is expected (the `Le` conversion
    // rule), and `leRefl x : Le x x` is accepted where `Lt (x - 1) x` is expected.
    const decrement = subMk(v("x"), K.intLitMk(1n));
    const leRefl = (e: K.Mk): K.Mk =>
      K.primMk(K.OP_BY_CONTRA, [e, e, K.lamMk("k", ltMk(e, e), K.farkasMk([v("k")], [1n]))]);
    const recursiveStep: K.Mk = K.lamMk(
      "x",
      intMk,
      K.lamMk(
        "px",
        leMk(K.intLitMk(0n), v("x")),
        K.lamMk(
          "ih",
          K.piMk(
            "y",
            intMk,
            K.piMk("py", leMk(K.intLitMk(0n), v("y")), K.piMk("d", ltMk(v("y"), v("x")), intMk)),
          ),
          K.primMk(
            K.OP_IF_LE,
            [
              intMk,
              K.intLitMk(1n),
              v("x"),
              K.lamMk(
                "h",
                leMk(K.intLitMk(1n), v("x")),
                K.appManyMk(v("ih"), [decrement, v("h"), leRefl(v("x"))]),
              ),
              K.lamMk("h2", ltMk(v("x"), K.intLitMk(1n)), K.intLitMk(0n)),
            ],
            0,
          ),
        ),
      ),
    );
    const measureIdentity = (): K.Mk => K.lamMk("z", intMk, v("z"));
    const term = K.mk(
      K.primMk(
        K.OP_FIX_WF,
        [intMk, motive(), measureIdentity(), recursiveStep, K.intLitMk(5n), leProofMk(0n, 5n)],
        0,
      ),
    );
    expect(K.checkType(env, term, K.Int).ok).toBe(true);
  });

  test("the measure proof argument is irrelevant", () => {
    const withProof = (proof: K.Mk): K.Term => applied(measure(), K.intLitMk(5n), proof);
    expect(conv(withProof(leProofMk(0n, 0n)), withProof(leProofMk(0n, 0n)))).toBe(true);
  });
});
