/**
 * Regression (fixc 2), unit level: equality in the obligation layer, in every orientation.
 *
 * The `===` in a loop invariant is an *equality hypothesis* to the obligations of the loop
 * body, and `src/vc/linear.ts` turns it into two `Le` rows by transporting along the equality
 * (`leOfEq`, the kernel's `J`).  The backward direction used to be built by transposing the
 * equality's sides instead of the motive, so it handed `J` a proof of `Eq Int b a` where
 * `Eq Int a b` was expected — the kernel rejected it, and *every* obligation whose hypotheses
 * mentioned the invariant failed, including the ones that had nothing to do with equality
 * (`measure-decrease: ((n - i) < (n - i)) may not hold`).
 *
 * These tests build the smallest contexts that show it: `a b (h : Eq Int a b)` and the two
 * `Le` directions, then `a b (h1 : a <= b) (h2 : b <= a)` and the `Eq` goal
 * (`proveEquality`/`intEq`, whose orientation was already right and is pinned here).
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import * as C from "../../src/vc/certify";
import * as L from "../../src/vc/linear";
import type { Obligation } from "../../src/vc/obligations";
import { checkClosed, env, names, span, whenZ3 } from "./helpers";

/** The binder at `position` of a `depth`-binder context, as a term of that context. */
const at = (position: number, depth: number): K.Term => K.varTerm(depth - 1 - position);

/** A kernel `Ctx` from binder domains, each written in the context of the preceding binders. */
function kernelContext(domains: readonly K.Term[]): K.Ctx {
  const types: K.Value[] = [];
  let values: K.Value[] = [];
  for (const domain of domains) {
    types.push(K.evalTerm(env, domain, values));
    values = [...values, K.vvar(values.length)];
  }
  return { env, types, values };
}

describe("the equality-hypothesis transport (`linearize`/`leOfEq`)", () => {
  // a : Int, b : Int, h : Eq Int a b — every domain in its own prefix context.
  const domains = [K.Int, K.Int, K.Eq(K.Int, K.varTerm(1), K.varTerm(0))];
  const depth = domains.length;
  const a = at(0, depth);
  const b = at(1, depth);
  const equality = { type: K.Int, lhs: a, rhs: b };

  for (const forward of [true, false]) {
    test(`the ${forward ? "forward" : "backward"} row is a proof the kernel accepts`, () => {
      const goal = forward ? K.Le(a, b) : K.Le(b, a);
      const proof = L.leOfEq(equality, K.varTerm(0), forward, 0);
      // 1. `J`'s rule, in the obligation's own ambient context.
      const checked = K.check(kernelContext(domains), proof, K.evalTerm(env, goal, L.contextValues(depth)));
      expect(checked.ok).toBe(true);
      if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
      // 2. The same proof, closed under its context, as the elaborator would hand it in.
      expect(checkClosed(domains, ["a", "b", "h"], proof, goal).ok).toBe(true);
    });
  }

  test("both rows agree with the proposition they are filed under", () => {
    const proposition = L.propositionOfTerm(env, depth, K.Eq(K.Int, a, b));
    expect(proposition.kind).toBe("eq");
    const linearized = L.linearize(env, depth, proposition, K.varTerm(0), 0);
    expect(linearized.complete).toBe(true);
    expect(linearized.entries.length).toBe(2);
    expect(linearized.entries.map((entry) => entry.text)).toEqual([
      `${K.formatTerm(a)} <= ${K.formatTerm(b)}`,
      `${K.formatTerm(b)} <= ${K.formatTerm(a)}`,
    ]);
    // Each row's proof proves the row's own proposition — in both directions.
    for (const entry of linearized.entries) {
      const goal = L.propositionTerm(entry.proposition);
      const checked = K.check(kernelContext(domains), entry.proof, K.evalTerm(env, goal, L.contextValues(depth)));
      expect(checked.ok).toBe(true);
      if (!checked.ok) throw new Error(`${entry.text}: ${K.formatKernelError(checked.error)}`);
    }
  });
});

describe("an `Eq` hypothesis in `certify`", () => {
  // a : Int, b : Int, h : Eq Int a b  |-  b <= a
  const domains = [K.Int, K.Int, K.Eq(K.Int, K.varTerm(1), K.varTerm(0))];
  const depth = domains.length;
  const a = at(0, depth);
  const b = at(1, depth);
  const obligation: Obligation = {
    id: "eq-hypothesis",
    kind: "post",
    span: span(),
    context: domains,
    hypotheses: [K.Eq(K.Int, a, b)],
    proofs: [K.varTerm(0)],
    goal: K.Le(b, a),
    atomNames: names(depth, ["a", "b", "h"]),
  };

  whenZ3("proves the backward `Le` through the equality's row", () => {
    const result = C.certify(env, obligation);
    expect(result.status).toBe("certified");
    if (result.proof === undefined) throw new Error(result.reason ?? "no proof");
    expect(checkClosed(domains, ["a", "b", "h"], result.proof, obligation.goal).ok).toBe(true);
  });

  whenZ3("proves the reversed equality itself", () => {
    // `h : Eq Int a b  |-  Eq Int b a`: the goal is proved through the hypothesis's rows, so
    // the transport and the goal orientation have to agree.
    const reversed: Obligation = { ...obligation, id: "eq-hypothesis-reversed", goal: K.Eq(K.Int, b, a) };
    const result = C.certify(env, reversed);
    expect(result.status).toBe("certified");
    if (result.proof === undefined) throw new Error(result.reason ?? "no proof");
    const checked = checkClosed(domains, ["a", "b", "h"], result.proof, reversed.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });
});

describe("a `!==` hypothesis is split into its two `Le` directions", () => {
  // x : Int, y : Int, h : Not (Eq Int x y), hle : x <= y  |-  x < y
  // (`splitDisequality` builds an `intEq` inside the split, so this pins that orientation too.)
  const domains = [
    K.Int,
    K.Int,
    K.Not(K.Eq(K.Int, K.varTerm(1), K.varTerm(0))),
    K.Le(K.varTerm(2), K.varTerm(1)),
  ];
  const depth = domains.length;
  const x = at(0, depth);
  const y = at(1, depth);
  const obligation: Obligation = {
    id: "disequality-split",
    kind: "post",
    span: span(),
    context: domains,
    hypotheses: [K.Not(K.Eq(K.Int, x, y)), K.Le(x, y)],
    proofs: [K.varTerm(1), K.varTerm(0)],
    goal: K.Lt(x, y),
    atomNames: names(depth, ["x", "y", "h", "hle"]),
  };

  whenZ3("is certified and the proof passes `K.checkType`", () => {
    const result = C.certify(env, obligation);
    expect(result.status).toBe("certified");
    if (result.proof === undefined) throw new Error(result.reason ?? "no proof");
    const checked = checkClosed(domains, ["x", "y", "h", "hle"], result.proof, obligation.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });
});

describe("an `Eq` goal (`proveEquality`/`intEq`)", () => {
  // a : Int, b : Int, h1 : a <= b, h2 : b <= a  |-  Eq Int a b
  // Each domain is written in its own prefix context: `h2`'s domain sees `a` at index 2 and
  // `b` at index 1 (`h1` is index 0 there).
  const domains = [K.Int, K.Int, K.Le(K.varTerm(1), K.varTerm(0)), K.Le(K.varTerm(1), K.varTerm(2))];
  const depth = domains.length;
  const a = at(0, depth);
  const b = at(1, depth);
  const obligation: Obligation = {
    id: "eq-goal",
    kind: "post",
    span: span(),
    context: domains,
    hypotheses: [K.Le(a, b), K.Le(b, a)],
    proofs: [K.varTerm(1), K.varTerm(0)],
    goal: K.Eq(K.Int, a, b),
    atomNames: names(depth, ["a", "b", "h1", "h2"]),
  };

  whenZ3("is certified with the two `Le` directions in the right order", () => {
    const result = C.certify(env, obligation);
    expect(result.status).toBe("certified");
    if (result.proof === undefined) throw new Error(result.reason ?? "no proof");
    // `intEq a b p q`: `p` proves `a <= b`, `q` proves `b <= a`.  A swapped `p`/`q` is a
    // kernel rejection, which the check below would report.
    const checked = checkClosed(domains, ["a", "b", "h1", "h2"], result.proof, obligation.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
    expect(K.formatTerm(result.proof)).toContain("intEq");
  });

  test("the goal term itself carries `a` on the left and `b` on the right", () => {
    // The orientation of the *goal* must stay `Eq Int a b` — a fix that transposed it (rather
    // than the proof) would certify the same obligations while elaborating the wrong theorem.
    const proposition = L.propositionOfTerm(env, depth, obligation.goal);
    expect(proposition.kind).toBe("eq");
    if (proposition.kind !== "eq") throw new Error("not an equality");
    expect(K.formatTerm(proposition.lhs)).toBe(K.formatTerm(a));
    expect(K.formatTerm(proposition.rhs)).toBe(K.formatTerm(b));
  });
});
