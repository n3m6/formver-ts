/**
 * Regression tests for atom keys (`src/kernel/linear.ts`).
 *
 * A key collision between two non-convertible values makes `Le` conversion identify two
 * different propositions, which lets the `Farkas` rule prove `Empty` — a soundness hole, not
 * merely a completeness one.  The hole this file guards against: a value substituted from a
 * closure environment used to be keyed one binder shallower than the enclosing traversal, so
 * a binder *inside* the substituted value printed the same `Bound(n)` as a binder of the term
 * being traversed.
 *
 *   V1 = fun a => fun b => a               (a closed term)
 *   V2 = fun c => g,  g = fun w => w       (g sits in the closure environment)
 *
 * Both used to key as `Lam(Int,Lam(Int,Bound(0)))` although `V1 1 0 = 1` and `V2 1 0 = 0`.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";

const env = K.emptyEnv();
const I = K.Int;
const intMk: K.Mk = () => K.Int;
const emptyMk: K.Mk = () => K.Empty;
const v = (name: string): K.Mk => K.varMk(name);

/** `(Int -> Int -> Int) -> Int`, the type of the function `h` the exploit quantifies over. */
const hType: K.Mk = K.piMk("_", intMk, K.piMk("_", intMk, intMk));

const gVal = K.evalTerm(env, K.lam("w", I, K.varTerm(0)), []);
const hVar = K.vvar(9);
/** `fun a => fun b => a`, a closed value. */
const v1Value = K.evalTerm(env, K.lam("a", I, K.lam("b", I, K.varTerm(1))), []);
/** `fun c => g` where `g`'s value (a `Lam`) comes from the closure environment. */
const v2Value = K.evalTerm(env, K.lam("c", I, K.varTerm(2)), [gVal, hVar]);

const key = (value: K.Value): string => K.keyOfValue(value, K.irrelevantOf);

describe("atom keys", () => {
  test("two non-convertible values do not share a key", () => {
    expect(key(v1Value)).not.toBe(key(v2Value));
    expect(K.convValue(env, 0, v1Value, v2Value)).toBe(false);
  });

  test("the two atoms `h V1` and `h V2` do not share a key", () => {
    const atom1 = K.evalTerm(env, K.app(K.varTerm(0), K.lam("a", I, K.lam("b", I, K.varTerm(1)))), [hVar]);
    const atom2 = K.evalTerm(env, K.app(K.varTerm(0), K.lam("c", I, K.varTerm(2))), [gVal, hVar]);
    expect(key(atom1)).not.toBe(key(atom2));
    expect(K.convValue(env, 0, atom1, atom2)).toBe(false);
  });

  test("`Le (h V1) 0` is not convertible with `Le (h V2) 0`", () => {
    const le1 = K.evalTerm(env, K.Le(K.app(K.varTerm(0), K.lam("a", I, K.lam("b", I, K.varTerm(1)))), K.intLit(0)), [gVal, hVar]);
    const le2 = K.evalTerm(env, K.Le(K.app(K.varTerm(0), K.lam("c", I, K.varTerm(2))), K.intLit(0)), [gVal, hVar]);
    expect(K.convValue(env, 2, le1, le2)).toBe(false);
  });

  test("the identity function is rejected at the type that needs the collision", () => {
    const V1Mk: K.Mk = K.lamMk("a", intMk, K.lamMk("b", intMk, v("a")));
    const V2Mk: K.Mk = K.lamMk("c", intMk, v("g"));
    const LeH1: K.Mk = K.primMk(K.OP_LE, [K.appMk(v("h"), V1Mk), K.intLitMk(0n)]);
    const LeH2: K.Mk = K.primMk(K.OP_LE, [K.appMk(v("h"), V2Mk), K.intLitMk(0n)]);
    const term = K.mk(
      K.letMk(
        "g",
        () => K.pi("_", I, I),
        K.lamMk("w", intMk, v("w")),
        K.lamMk("h", hType, K.lamMk("p", LeH1, v("p"))),
      ),
    );
    const type = K.mk(
      K.letMk(
        "g",
        () => K.pi("_", I, I),
        K.lamMk("w", intMk, v("w")),
        K.piMk("h", hType, K.piMk("p", LeH1, LeH2)),
      ),
    );
    expect(K.checkType(env, term, type).ok).toBe(false);
  });

  test("Farkas cannot turn the collision into a proof of Empty", () => {
    const V1Mk: K.Mk = K.lamMk("a", intMk, K.lamMk("b", intMk, v("a")));
    const V2Mk: K.Mk = K.lamMk("c", intMk, v("g"));
    const F1: K.Mk = K.primMk(K.OP_LE, [K.primMk(K.OP_ADD, [K.appMk(v("h"), V1Mk), K.intLitMk(5n)]), K.intLitMk(0n)]);
    const F2: K.Mk = K.primMk(K.OP_LE, [K.intLitMk(0n), K.appMk(v("h"), V2Mk)]);
    const proof = K.mk(
      K.letMk(
        "g",
        () => K.pi("_", I, I),
        K.lamMk("w", intMk, v("w")),
        K.lamMk(
          "h",
          hType,
          K.lamMk("p1", F1, K.lamMk("p2", F2, K.farkasMk([v("p1"), v("p2")], [1n, 1n]))),
        ),
      ),
    );
    const type = K.mk(
      K.letMk(
        "g",
        () => K.pi("_", I, I),
        K.lamMk("w", intMk, v("w")),
        K.piMk("h", hType, K.piMk("p1", F1, K.piMk("p2", F2, emptyMk))),
      ),
    );
    expect(K.checkType(env, proof, type).ok).toBe(false);
  });

  test("alpha-equivalent values still share a key (completeness is preserved)", () => {
    const alpha1 = K.evalTerm(env, K.lam("a", I, K.lam("b", I, K.varTerm(1))), []);
    const alpha2 = K.evalTerm(env, K.lam("x", I, K.lam("y", I, K.varTerm(1))), []);
    expect(key(alpha1)).toBe(key(alpha2));
    expect(K.convValue(env, 0, alpha1, alpha2)).toBe(true);
  });

  test("a neutral substituted from a closure environment keys like the neutral itself", () => {
    const substituted = K.evalTerm(env, K.varTerm(0), [hVar]);
    expect(key(substituted)).toBe(key(hVar));
  });

  /**
   * The nested case: a value substituted from one environment can itself contain a value
   * substituted from another, so a *fixed* substitution namespace is not enough — every
   * level must extend it.  `V1 = let gp = fun z y => z in fun a => gp` and
   * `V2 = let h = fun w => w in let g = fun d => h in fun c => g` are not convertible
   * (`V1 1 2 3 = 2`, `V2 1 2 3 = 3`), and used to share a key.
   */
  const mkV1: K.Mk = K.letMk(
    "gp",
    () => K.pi("_", I, K.pi("_", I, I)),
    K.lamMk("z", intMk, K.lamMk("y", intMk, v("z"))),
    K.lamMk("a", intMk, v("gp")),
  );
  const mkV2: K.Mk = K.letMk(
    "h",
    () => K.pi("_", I, I),
    K.lamMk("w", intMk, v("w")),
    K.letMk(
      "g",
      () => K.pi("_", I, K.pi("_", I, I)),
      K.lamMk("d", intMk, v("h")),
      K.lamMk("c", intMk, v("g")),
    ),
  );

  test("nested environment substitutions do not share a key either", () => {
    const v1 = K.evalTerm(env, K.mk(mkV1), []);
    const v2 = K.evalTerm(env, K.mk(mkV2), []);
    expect(key(v1)).not.toBe(key(v2));
    expect(K.convValue(env, 0, v1, v2)).toBe(false);
  });

  test("Farkas cannot exploit the nested case to prove Empty", () => {
    const h0Type: K.Mk = K.piMk("_", intMk, K.piMk("_", intMk, intMk));
    const HV1: K.Mk = K.appMk(v("h0"), mkV1);
    const HV2: K.Mk = K.appMk(v("h0"), mkV2);
    const F1: K.Mk = K.primMk(K.OP_LE, [K.primMk(K.OP_ADD, [HV1, K.intLitMk(5n)]), K.intLitMk(0n)]);
    const F2: K.Mk = K.primMk(K.OP_LE, [K.intLitMk(0n), HV2]);
    const context = (inner: K.Mk): K.Mk =>
      K.letMk(
        "h",
        () => K.pi("_", I, I),
        K.lamMk("w", intMk, v("w")),
        K.letMk(
          "g",
          () => K.pi("_", I, K.pi("_", I, I)),
          K.lamMk("d", intMk, v("h")),
          K.letMk(
            "gp",
            () => K.pi("_", I, K.pi("_", I, I)),
            K.lamMk("z", intMk, K.lamMk("y", intMk, v("z"))),
            inner,
          ),
        ),
      );
    const proof = K.mk(
      context(
        K.lamMk("h0", h0Type, K.lamMk("p1", F1, K.lamMk("p2", F2, K.farkasMk([v("p1"), v("p2")], [1n, 1n])))),
      ),
    );
    const type = K.mk(context(K.piMk("h0", h0Type, K.piMk("p1", F1, K.piMk("p2", F2, emptyMk)))));
    expect(K.checkType(env, proof, type).ok).toBe(false);
  });
});
