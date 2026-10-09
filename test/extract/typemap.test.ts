/**
 * Milestone 5: the type mapping of section 6.3.
 *
 * The mapping is checked two ways: the mapped type of `clamp` is compared with the exact type
 * the specification prints, and the kernel is asked to accept a hand-built inhabitant of the
 * mapped codomain.  Every `examples/pass` signature must be a well-formed kernel type.
 */
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import * as K from "../../src/kernel/index";
import type { Mk } from "../../src/kernel/index";
import { Ids, exprTerm, extractFile } from "../../src/extract/fragment";

const repoRoot = resolve(import.meta.dir, "../..");
const env = K.emptyEnv();

function extract(relative: string) {
  const path = resolve(repoRoot, relative);
  return extractFile(path, readFileSync(path, "utf8"));
}

const intMk: Mk = () => K.Int;
const type0Mk: Mk = K.sortMk(0);
const v = (name: string): Mk => K.varMk(name);
const le = (a: Mk, b: Mk): Mk => K.primMk(K.OP_LE, [a, b]);
const vec = (a: Mk, n: Mk): Mk => K.primMk(K.OP_VEC, [a, n]);
const add = (a: Mk, b: Mk): Mk => K.primMk(K.OP_ADD, [a, b]);
const eq = (a: Mk, x: Mk, y: Mk): Mk => K.primMk(K.OP_EQ, [a, x, y]);
const inRange = (x: Mk): Mk => K.appMk(K.constMk(K.IN_RANGE_NAME), x);
const and = (a: Mk, b: Mk): Mk => K.appManyMk(K.constMk(K.AND_NAME), [a, b]);

describe("clamp", () => {
  const fn = extract("examples/pass/clamp.ts").functions.find((f) => f.name === "clamp")!;

  /**
   * The type printed in specification 6.3:
   *
   *   (x : Int) -> InRange x -> (lo : Int) -> InRange lo -> (hi : Int) -> InRange hi
   *   -> Le lo hi -> Sigma (r : Int). And (InRange r) (And (Le lo r) (Le r hi))
   */
  const expected = K.mk(
    K.piMk(
      "x",
      intMk,
      K.piMk(
        "rx",
        inRange(v("x")),
        K.piMk(
          "lo",
          intMk,
          K.piMk(
            "rlo",
            inRange(v("lo")),
            K.piMk(
              "hi",
              intMk,
              K.piMk(
                "rhi",
                inRange(v("hi")),
                K.piMk(
                  "pre",
                  le(v("lo"), v("hi")),
                  K.sigmaMk(
                    "r",
                    intMk,
                    and(inRange(v("r")), and(le(v("lo"), v("r")), le(v("r"), v("hi")))),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    ),
  );

  test("the mapped type is the type of section 6.3, up to conversion", () => {
    expect(K.isConvertible(env, fn.signature.type, expected)).toBe(true);
    expect(K.isTypeTerm(env, fn.signature.type).ok).toBe(true);
  });

  test("the binder telescope is exactly the parameters, their proofs and the precondition", () => {
    expect(
      fn.signature.binders.map((b) => ({ name: b.name, role: b.role })),
    ).toEqual([
      { name: "x", role: "param" },
      { name: "r_x", role: "in-range" },
      { name: "lo", role: "param" },
      { name: "r_lo", role: "in-range" },
      { name: "hi", role: "param" },
      { name: "r_hi", role: "in-range" },
      { name: "pre0", role: "pre" },
    ]);
    expect(fn.signature.result.shape).toBe("int");
    expect(fn.signature.result.layout.valuePath).toEqual([0]);
    expect(fn.signature.result.layout.inRangePath).toEqual([1, 0]);
    expect(fn.signature.result.layout.postPath).toEqual([1, 1]);
  });

  test("the kernel accepts a hand-built inhabitant of the mapped codomain", () => {
    const five = K.intLit(5n);
    const codomain = K.sigma(
      "r",
      K.Int,
      K.And(K.InRange(K.varTerm(0)), K.And(K.Le(K.intLit(0n), K.varTerm(0)), K.Le(K.varTerm(0), K.intLit(10n)))),
    );
    const inRangeProof = K.pair(K.InRange(five), K.LeProof(-K.SAFE_MAX, 5n), K.LeProof(5n, K.SAFE_MAX));
    const postProof = K.pair(
      K.And(K.Le(K.intLit(0n), five), K.Le(five, K.intLit(10n))),
      K.LeProof(0n, 5n),
      K.LeProof(5n, 10n),
    );
    const postType = K.And(K.Le(K.intLit(0n), five), K.Le(five, K.intLit(10n)));
    const value = K.pair(codomain, five, K.pair(K.And(K.InRange(five), postType), inRangeProof, postProof));
    const checked = K.checkType(env, value, codomain);
    expect(checked.ok ? "ok" : checked.error.message).toBe("ok");
  });

  test("a wrong result proves nothing: swapping the bounds is rejected", () => {
    const swapped = K.mk(
      K.piMk(
        "x",
        intMk,
        K.piMk(
          "rx",
          inRange(v("x")),
          K.piMk(
            "lo",
            intMk,
            K.piMk(
              "rlo",
              inRange(v("lo")),
              K.piMk(
                "hi",
                intMk,
                K.piMk(
                  "rhi",
                  inRange(v("hi")),
                  K.piMk(
                    "pre",
                    le(v("lo"), v("hi")),
                    K.sigmaMk(
                      "r",
                      intMk,
                      and(inRange(v("r")), and(le(v("r"), v("lo")), le(v("hi"), v("r")))),
                    ),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    );
    expect(K.isConvertible(env, fn.signature.type, swapped)).toBe(false);
  });
});

describe("concat", () => {
  const fn = extract("examples/pass/concat.ts").functions.find((f) => f.name === "concat")!;

  test("a returned array is `Sigma (m : Int). And (Vec T m) posts`", () => {
    const expected = K.mk(
      K.piMk(
        "T",
        type0Mk,
        K.piMk(
          "n_a",
          intMk,
          K.piMk(
            "a",
            vec(v("T"), v("n_a")),
            K.piMk(
              "n_b",
              intMk,
              K.piMk(
                "b",
                vec(v("T"), v("n_b")),
                K.piMk(
                  "pre0",
                  le(add(v("n_a"), v("n_b")), K.intLitMk(K.MAX_VEC_LEN)),
                  K.sigmaMk("m", intMk, and(vec(v("T"), v("m")), eq(intMk, v("m"), add(v("n_a"), v("n_b"))))),
                ),
              ),
            ),
          ),
        ),
      ),
    );
    expect(K.isConvertible(env, fn.signature.type, expected)).toBe(true);
    expect(K.isTypeTerm(env, fn.signature.type).ok).toBe(true);
    expect(fn.signature.result.shape).toBe("vec");
    expect(fn.signature.result.layout).toMatchObject({
      lengthPath: [0],
      vecPath: [1, 0],
      postPath: [1, 1],
    });
  });

  test("`a.length` maps to the length binder, so the precondition is `Le (n_a + n_b) 4294967295`", () => {
    const pre = fn.signature.preconditions[0]!;
    expect(pre.text).toBe("((a.length + b.length) <= 4294967295)");
    const ctx = {
      binders: fn.signature.binders.slice(0, 5),
      facts: [],
      narrowings: [],
      ids: new Ids(),
    };
    // `T` is at index 4, `n_a` at 3, `a` at 2, `n_b` at 1 and `b` at 0 in that context.
    const expected = K.Le(K.Add(K.varTerm(3), K.varTerm(1)), K.intLit(K.MAX_VEC_LEN));
    expect(K.formatTerm(exprTerm(ctx, pre.prop))).toBe(K.formatTerm(expected));
  });
});

describe("binarySearch", () => {
  const fn = extract("examples/pass/binarySearch.ts").functions.find((f) => f.name === "binarySearch")!;

  test("the mapped type is well-formed and mentions the element guard", () => {
    const checked = K.isTypeTerm(env, fn.signature.type);
    expect(checked.ok ? "ok" : checked.error.message).toBe("ok");
    const printed = K.formatTerm(fn.signature.type);
    expect(printed).toContain("elems_a");
    expect(printed).toContain("InRange (get(Int(), n_a, a, i, p))");
    expect(printed).toContain("Vec(Int(), n_a)");
  });

  test("the result packs the value, its InRange proof and the postcondition", () => {
    const result = fn.signature.result;
    expect(result.shape).toBe("int");
    expect(result.layout.valuePath).toEqual([0]);
    expect(result.layout.inRangePath).toEqual([1, 0]);
    expect(result.layout.postPath).toEqual([1, 1]);
    expect(result.posts[0]!.text).toBe("((-1 <= result) && (result < a.length))");
  });
});

describe("every example signature", () => {
  for (const file of [
    "clamp.ts",
    "abs.ts",
    "safeGet.ts",
    "concat.ts",
    "take.ts",
    "binarySearch.ts",
    "sumTo.ts",
    "shape.ts",
    "useClamp.ts",
  ]) {
    test(`${file}: the mapped type is a well-formed kernel type`, () => {
      for (const fn of extract(`examples/pass/${file}`).functions) {
        const checked = K.isTypeTerm(env, fn.signature.type);
        expect({ fn: fn.name, error: checked.ok ? null : checked.error.message }).toEqual({
          fn: fn.name,
          error: null,
        });
      }
    });
  }
});
