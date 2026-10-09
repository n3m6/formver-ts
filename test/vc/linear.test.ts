/**
 * `src/vc/linear.ts` against the kernel's frozen arithmetic.
 *
 * `linear.ts` deliberately duplicates `tightenRow`, `checkCertificate` and `rowOfLe`, so the
 * one thing these tests must establish is that the copies agree *exactly*: same atom keys,
 * same coefficients, same bounds, same tightening (specification sections 6.1.4 and 12).
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import * as L from "../../src/vc/linear";
import { env } from "./helpers";

const depth = 4;
const values = L.contextValues(depth);
const x = K.varTerm(3);
const y = K.varTerm(2);

/** A stable, order-independent rendering of a coefficient record. */
const entries = (a: Readonly<Record<string, bigint>>): [string, string][] =>
  Object.entries(a)
    .filter(([, coefficient]) => coefficient !== 0n)
    .map(([key, coefficient]) => [key, coefficient.toString()] as [string, string])
    .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));

describe("tightenRow agrees with the kernel", () => {
  const corpus: K.Row[] = [
    { a: { x: 2n }, b: 1n },
    { a: { x: 2n }, b: 2n },
    { a: { x: -2n }, b: -1n },
    { a: { x: -2n }, b: -2n },
    { a: { x: 4n, y: -6n }, b: 3n },
    { a: { x: 3n, y: 2n }, b: 5n },
    { a: {}, b: 4n },
    { a: {}, b: -4n },
    { a: { x: 0n, y: 3n }, b: 5n },
    { a: { x: 0n, y: 0n }, b: 7n },
    { a: { x: -6n, y: 9n, z: -3n }, b: 4n },
    { a: { x: 1n, y: -1n }, b: -5n },
    { a: { x: 1000000n }, b: 999999n },
    { a: { x: 2n, y: 0n, z: 4n }, b: -3n },
    { a: Object.fromEntries([["__proto__", 2n]]), b: 1n },
  ];

  for (const row of corpus) {
    test(`tighten ${JSON.stringify(entries(row.a).map(([k, c]) => `${c}${k}`))} <= ${row.b}`, () => {
      const kernel = K.tightenRow(row);
      const mine = L.tightenRow(row);
      expect(entries(mine.a)).toEqual(entries(kernel.a));
      expect(mine.b).toBe(kernel.b);
    });
  }

  test("tightening is what makes `2x <= 1` and `2x >= 1` contradictory", () => {
    const rows = [L.tightenRow({ a: { x: 2n }, b: 1n }), L.tightenRow({ a: { x: -2n }, b: -1n })];
    expect(rows).toEqual([
      { a: { x: 1n }, b: 0n },
      { a: { x: -1n }, b: -1n },
    ]);
    expect(L.checkCertificate(rows, [1n, 1n])).toBe(true);
    // `2x <= 2` and `2x >= 2` are satisfied by x = 1 and stay unrefuted.
    const satisfiable = [L.tightenRow({ a: { x: 2n }, b: 2n }), L.tightenRow({ a: { x: -2n }, b: -2n })];
    expect(satisfiable).toEqual([
      { a: { x: 1n }, b: 1n },
      { a: { x: -1n }, b: -1n },
    ]);
    expect(L.checkCertificate(satisfiable, [1n, 1n])).toBe(false);
    expect(L.checkCertificate(satisfiable, [0n, 0n])).toBe(false);
  });

  test("checkCertificate agrees with the kernel on the same corpus", () => {
    const rows: K.Row[] = [
      { a: { x: 1n }, b: 1n },
      { a: { x: -1n }, b: -2n },
      { a: {}, b: 0n },
    ];
    const multipliers: bigint[][] = [[1n, 1n, 0n], [1n, 1n, 5n], [2n, 2n, 0n], [-1n, 1n, 0n], [1n], [1n, 1n, 1n, 1n]];
    for (const lambda of multipliers) {
      expect(L.checkCertificate(rows, lambda)).toBe(K.checkCertificate(rows, lambda));
    }
  });
});

describe("rows agree with the kernel's rowOfLe", () => {
  const propositions: [string, K.Term][] = [
    ["2x <= 1", K.Le(K.MulConst(K.intLit(2n), x), K.intLit(1n))],
    ["2x <= 2", K.Le(K.MulConst(K.intLit(2n), x), K.intLit(2n))],
    ["-x <= 0", K.Le(K.Neg(x), K.intLit(0n))],
    ["x <= -1", K.Le(x, K.intLit(-1n))],
    ["0 <= x", K.Le(K.intLit(0n), x)],
    ["x <= y", K.Le(x, y)],
    ["x - y <= 0", K.Le(K.Sub(x, y), K.intLit(0n))],
    ["4x - 6y <= 3", K.Le(K.Sub(K.MulConst(K.intLit(4n), x), K.MulConst(K.intLit(6n), y)), K.intLit(3n))],
    ["0x + 0y <= 5", K.Le(K.Add(K.MulConst(K.intLit(0n), x), K.MulConst(K.intLit(0n), y)), K.intLit(5n))],
    ["x <= x", K.Le(x, x)],
    ["5 <= 4", K.Le(K.intLit(5n), K.intLit(4n))],
    ["2x < 1", K.Lt(K.MulConst(K.intLit(2n), x), K.intLit(1n))],
    ["-3x - 3y <= -6", K.Le(K.Neg(K.MulConst(K.intLit(3n), K.Add(x, y))), K.intLit(-6n))],
    ["2*(x+y) <= 3", K.Le(K.MulConst(K.intLit(2n), K.Add(x, y)), K.intLit(3n))],
    [
      "get A n v i p <= 0",
      K.Le(K.Get(K.Int, K.varTerm(1), K.varTerm(2), K.varTerm(3), K.varTerm(0)), K.intLit(0n)),
    ],
  ];

  for (const [label, proposition] of propositions) {
    test(label, () => {
      const value = K.evalTerm(env, proposition, values);
      const kernel = K.rowOfLe(value);
      expect(kernel.ok).toBe(true);
      if (!kernel.ok) return;
      const mine = L.rowOfValue(value)!;
      expect(entries(mine.a)).toEqual(entries(kernel.value.a));
      expect(mine.b).toBe(kernel.value.b);
      // The term-level path (what `linearize` uses) must agree too.
      const head = (value as { head: { args: readonly K.Value[] } }).head;
      const fromTerms = L.rowOfLeTerms(env, depth, K.quote(env, depth, head.args[0]!), K.quote(env, depth, head.args[1]!));
      expect(entries(fromTerms.a)).toEqual(entries(kernel.value.a));
      expect(fromTerms.b).toBe(kernel.value.b);
      // Tightening and the certificate check are the kernel's, on the same row.
      expect(entries(L.tightenRow(mine).a)).toEqual(entries(K.tightenRow(kernel.value).a));
    });
  }

  test("atom keys are the kernel's keys, including proof-argument erasure", () => {
    const withOneProof = K.evalTerm(
      env,
      K.Le(K.Get(K.Int, K.varTerm(1), K.varTerm(2), K.varTerm(3), K.varTerm(0)), K.intLit(0n)),
      values,
    );
    // The same `get`, but with a different (irrelevant) bounds proof.
    const withOtherProof = K.evalTerm(
      env,
      K.Le(K.Get(K.Int, K.varTerm(1), K.varTerm(2), K.varTerm(3), K.IntEq(K.intLit(0n), K.intLit(0n), K.LeProof(0n, 0n), K.LeProof(0n, 0n))), K.intLit(0n)),
      values,
    );
    const first = L.rowOfValue(withOneProof)!;
    const second = L.rowOfValue(withOtherProof)!;
    // `get`'s proof argument is irrelevant: the two atoms are the same key.
    expect(Object.keys(first.a)).toEqual(Object.keys(second.a));
    expect(entries(first.a)).toEqual(entries(second.a));
  });
});

describe("forms and propositions", () => {
  test("form arithmetic mirrors the kernel's linear values", () => {
    const formOf = (term: K.Term): L.Form => L.formOfTerm(env, term, depth);
    expect(L.formEquals(formOf(K.Add(x, x)), L.formScale(formOf(x), 2n))).toBe(true);
    expect(L.formEquals(formOf(K.Sub(K.Add(x, y), y)), formOf(x))).toBe(true);
    expect(L.formEquals(formOf(K.Neg(K.Neg(x))), formOf(x))).toBe(true);
    expect(L.formEquals(L.formAdd(formOf(x), formOf(K.intLit(1n))), formOf(K.Add(x, K.intLit(1n))))).toBe(true);
    expect(L.formEquals(formOf(K.Sub(x, x)), { k: 0n, atoms: new Map() })).toBe(true);
    expect(L.formEquals(formOf(K.MulConst(K.intLit(3n), K.Add(x, y))), formOf(K.Add(K.MulConst(K.intLit(3n), x), K.MulConst(K.intLit(3n), y))))).toBe(true);
  });

  test("propositions are decomposed from their kernel values", () => {
    const range = L.propositionOfTerm(env, 2, K.InRange(K.varTerm(1)));
    expect(range.kind).toBe("and");
    if (range.kind === "and") {
      expect(range.first.kind).toBe("le");
      expect(range.second.kind).toBe("le");
      expect(L.propositionText(range.second)).toBe(`?1 <= ${K.SAFE_MAX}`);
    }
    const strict = L.propositionOfTerm(env, 2, K.Lt(K.varTerm(1), K.varTerm(0)));
    expect(strict.kind).toBe("le");
    const disjunction = L.propositionOfTerm(env, 2, K.Sum(K.Le(K.varTerm(1), K.intLit(0n)), K.Le(K.intLit(1n), K.varTerm(1))));
    expect(disjunction.kind).toBe("sum");
    const negation = L.propositionOfTerm(env, 2, K.Not(K.Eq(K.Int, K.varTerm(1), K.intLit(0n))));
    expect(negation.kind).toBe("not");
    expect(L.propositionOfTerm(env, 0, K.Unit).kind).toBe("unit");
    expect(L.propositionOfTerm(env, 2, K.And(K.Le(K.varTerm(1), K.intLit(0n)), K.Unit)).kind).toBe("and");
  });

  test("comparison candidates come from the `Le` boundaries of a goal", () => {
    const disjunction = L.propositionOfTerm(
      env,
      2,
      K.Sum(K.Le(K.varTerm(1), K.intLit(0n)), K.Le(K.intLit(1n), K.varTerm(1))),
    );
    const candidates = L.comparisonCandidates(disjunction);
    expect(candidates.length).toBe(2);
    expect(K.formatTerm(candidates[0]!.lhs)).toBe("?1");
    expect(K.formatTerm(candidates[1]!.lhs)).toBe("1");
  });

  test("shift, occursFree and unbind are inverse enough for splitting", () => {
    const term = K.Le(K.Add(K.varTerm(1), K.intLit(1n)), K.varTerm(0));
    expect(L.maxFreeIndex(term)).toBe(1);
    expect(L.maxFreeIndex(K.Le(K.varTerm(2), K.varTerm(0)))).toBe(2);
    expect(L.occursFree(K.Le(K.varTerm(1), K.varTerm(0)), 0)).toBe(true);
    expect(L.occursFree(K.Le(K.varTerm(1), K.varTerm(2)), 0)).toBe(false);
    const shifted = L.shift(term, 2);
    expect(K.formatTerm(shifted)).toBe(K.formatTerm(K.Le(K.Add(K.varTerm(3), K.intLit(1n)), K.varTerm(2))));
    // Inside the lambda, `Var 1` is the outer index 0; `Var 0` is the binder itself.
    expect(L.occursFree(K.lam("z", K.Int, K.varTerm(1)), 0)).toBe(true);
    expect(L.occursFree(K.lam("z", K.Int, K.varTerm(0)), 0)).toBe(false);
    // `unbind` (and the general `dropBinders`) move a free variable down by one binder.
    const sigma = K.sigma("a", K.Int, K.Le(K.varTerm(1), K.intLit(0n)));
    expect(sigma.tag).toBe("Sigma");
    expect(K.formatTerm(L.unbind(K.Le(K.varTerm(2), K.varTerm(0))))).toBe(
      K.formatTerm(K.Le(K.varTerm(1), K.varTerm(0))),
    );
    expect(K.formatTerm(L.dropBinders(K.Le(K.varTerm(3), K.intLit(0n)), 3))).toBe(
      K.formatTerm(K.Le(K.varTerm(0), K.intLit(0n))),
    );
  });
});
