/**
 * `src/vc/certify.ts` — the acceptance list of specification section 9.3.
 *
 * Every valid obligation is checked twice: `certify` reports `certified`, and the proof it
 * returned is closed under its ambient context and handed to `K.checkType`, which is exactly
 * what the kernel will do with it inside the elaborated function (section 6.5).
 *
 * Obligations are written the way the elaborator will build them: the domains passed to
 * `makeContext` are written in the *full* ambient context and moved into the
 * preceding-binders context by `dropBinders`, so a test only ever writes one form of each
 * proposition.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import * as C from "../../src/vc/certify";
import * as L from "../../src/vc/linear";
import type { Obligation } from "../../src/vc/obligations";
import { checkClosed, env, names, span, whenZ3 } from "./helpers";

/** The binder at `position` of a `depth`-binder context, as a term of that context. */
const at = (position: number, depth: number): K.Term => K.varTerm(depth - 1 - position);

/**
 * A context of `depth` binders from their domains, each written in the *full* context
 * (`Int` for a value binder); the domain of the binder at position `p` is moved down by
 * `depth - p` binders, which is what the kernel's `Ctx` stores.
 */
function makeContext(depth: number, domains: readonly K.Term[]): K.Term[] {
  if (domains.length !== depth) throw new Error(`expected ${depth} domains, got ${domains.length}`);
  return domains.map((domain, position) => L.dropBinders(domain, depth - position));
}

/** The kernel's view of a `Le`-goaled certificate: its hypotheses' types plus the negation. */
function kernelHypTypes(ob: Obligation, negatedGoal: K.Term): K.Value[] {
  const values = L.contextValues(ob.context?.length ?? 0);
  return [...ob.hypotheses, negatedGoal].map((term) => K.evalTerm(env, term, values));
}

const numeric = (counterexample: Readonly<Record<string, string>>, name: string): bigint => {
  const value = counterexample[name];
  if (value === undefined) {
    throw new Error(`the counterexample has no ${name}: ${JSON.stringify(counterexample)}`);
  }
  return BigInt(value);
};

// ---------------------------------------------------------------------------
// The bounds VC: 0 <= i < n  |-  i + 1 <= n
// ---------------------------------------------------------------------------

const boundsDepth = 4;
const i0 = at(0, boundsDepth);
const n0 = at(1, boundsDepth);
const boundsContext = makeContext(boundsDepth, [K.Int, K.Int, K.Le(K.intLit(0n), i0), K.Lt(i0, n0)]);
const boundsObligation: Obligation = {
  id: "bounds",
  kind: "index",
  span: span(4, 12),
  context: boundsContext,
  hypotheses: [K.Le(K.intLit(0n), i0), K.Lt(i0, n0)],
  goal: K.Le(K.Add(i0, K.intLit(1n)), n0),
  atomNames: names(boundsDepth, ["i", "n", "h1", "h2"]),
};

describe("the bounds VC", () => {
  whenZ3("is certified with a certificate the kernel's farkas.ts accepts", () => {
    const result = C.certify(env, boundsObligation);
    expect(result.status).toBe("certified");
    expect(result.proof).toBeDefined();
    expect(result.proofType).toBe(boundsObligation.goal);
    expect(result.multipliers).toEqual([0n, 1n, 1n]);
    // The kernel's own rule, on the kernel's own rows: `Lt n (i + 1)` is the `no` branch.
    const hypTypes = kernelHypTypes(boundsObligation, K.Lt(n0, K.Add(i0, K.intLit(1n))));
    expect(K.checkFarkas({ hypTypes, coeffs: result.multipliers! }).ok).toBe(true);
  });

  whenZ3("produces a proof that `K.checkType` accepts", () => {
    const result = C.certify(env, boundsObligation);
    const checked = checkClosed(boundsContext, ["i", "n", "h1", "h2"], result.proof!, boundsObligation.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });

  whenZ3("rejects a forged certificate for the same rows", () => {
    const hypTypes = kernelHypTypes(boundsObligation, K.Lt(n0, K.Add(i0, K.intLit(1n))));
    // Right shape, but the bound does not come out negative.
    expect(K.checkFarkas({ hypTypes, coeffs: [1n, 1n, 1n] }).ok).toBe(false);
    // Negative multipliers are never certificates.
    expect(K.checkFarkas({ hypTypes, coeffs: [1n, 1n, -1n] }).ok).toBe(false);
    // The wrong number of multipliers is a shape error.
    expect(K.checkFarkas({ hypTypes, coeffs: [1n, 1n] }).ok).toBe(false);
    // ... and this module's copy of the arithmetic agrees, row by row.
    const rows = [
      L.tightenRow(L.rowOfLeTerms(env, boundsDepth, K.intLit(0n), i0)),
      L.tightenRow(L.rowOfLeTerms(env, boundsDepth, K.Add(i0, K.intLit(1n)), n0)),
      L.tightenRow(L.rowOfLeTerms(env, boundsDepth, K.Add(n0, K.intLit(1n)), K.Add(i0, K.intLit(1n)))),
    ];
    expect(L.checkCertificate(rows, [0n, 1n, 1n])).toBe(true);
    expect(L.checkCertificate(rows, [1n, 1n, 1n])).toBe(false);
    expect(L.checkCertificate(rows, [1n, 1n, -1n])).toBe(false);
  });

  whenZ3("certifies with the documented innermost-hypothesis fallback when no context is given", () => {
    const bare: Obligation = {
      id: "bounds-bare",
      kind: "index",
      span: span(),
      hypotheses: [K.Le(K.intLit(0n), i0), K.Lt(i0, n0)],
      goal: K.Le(K.Add(i0, K.intLit(1n)), n0),
      // `proofs` omitted and no `context`: the hypotheses are the innermost binders.
    };
    const result = C.certify(env, bare);
    expect(result.status).toBe("certified");
    const checked = checkClosed(boundsContext, ["i", "n", "h1", "h2"], result.proof!, bare.goal);
    expect(checked.ok).toBe(true);
  });
});

// ---------------------------------------------------------------------------
// clamp
// ---------------------------------------------------------------------------

// The `x < lo` branch returns `lo`; context: x, r_x, lo, r_lo, hi, r_hi, pre0, h.
const clampDepth = 8;
const cx = at(0, clampDepth);
const clo = at(2, clampDepth);
const chi = at(4, clampDepth);
const clampContext = makeContext(clampDepth, [
  K.Int,
  K.InRange(cx),
  K.Int,
  K.InRange(clo),
  K.Int,
  K.InRange(chi),
  K.Le(clo, chi),
  K.Le(K.Add(cx, K.intLit(1n)), clo),
]);
const clampProofObligation: Obligation = {
  id: "clamp-lo",
  kind: "post",
  span: span(6, 15),
  context: clampContext,
  hypotheses: [K.InRange(cx), K.InRange(clo), K.InRange(chi), K.Le(clo, chi), K.Le(K.Add(cx, K.intLit(1n)), clo)],
  goal: K.And(K.InRange(clo), K.And(K.Le(clo, clo), K.Le(clo, chi))),
  atomNames: names(clampDepth, ["x", "r_x", "lo", "r_lo", "hi", "r_hi", "pre0", "h"]),
};
const clampNames = ["x", "r_x", "lo", "r_lo", "hi", "r_hi", "pre0", "h"];

// The `x > hi` branch returns `hi`, with no precondition; context: x, r_x, lo, r_lo, hi, r_hi, h.
const noPreDepth = 7;
const nx = at(0, noPreDepth);
const nlo = at(2, noPreDepth);
const nhi = at(4, noPreDepth);
const clampNoPreContext = makeContext(noPreDepth, [
  K.Int,
  K.InRange(nx),
  K.Int,
  K.InRange(nlo),
  K.Int,
  K.InRange(nhi),
  K.Lt(nhi, nx),
]);
const clampNoPreObligation: Obligation = {
  id: "clamp-hi",
  kind: "post",
  span: span(7, 15),
  context: clampNoPreContext,
  hypotheses: [K.InRange(nx), K.InRange(nlo), K.InRange(nhi), K.Lt(nhi, nx)],
  goal: K.And(K.InRange(nhi), K.And(K.Le(nlo, nhi), K.Le(nhi, nhi))),
  atomNames: names(noPreDepth, ["x", "r_x", "lo", "r_lo", "hi", "r_hi", "h"]),
};

describe("clamp", () => {
  whenZ3("with its precondition, the `x < lo` branch is certified", () => {
    const result = C.certify(env, clampProofObligation);
    expect(result.status).toBe("certified");
    const checked = checkClosed(clampContext, clampNames, result.proof!, clampProofObligation.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });

  whenZ3("without the precondition, the `x > hi` branch is invalid with a real counterexample", () => {
    const result = C.certify(env, clampNoPreObligation);
    expect(result.status).toBe("failed");
    expect(result.proof).toBeUndefined();
    const counterexample = result.counterexample!;
    expect(counterexample).toBeDefined();
    // Reported over the user's names, not Z3's.
    expect(Object.keys(counterexample).sort()).toEqual(["hi", "lo", "x"]);
    // Evaluate the counterexample against the spec instead of comparing literal values.
    const x = numeric(counterexample, "x");
    const lo = numeric(counterexample, "lo");
    const hi = numeric(counterexample, "hi");
    const returned = hi; // this branch returns `hi`
    expect(hi < x).toBe(true); // it is on this branch (`x > hi`)
    expect(-K.SAFE_MAX <= hi && hi <= K.SAFE_MAX).toBe(true); // `InRange hi` holds
    expect(lo <= returned && returned <= hi).toBe(false); // ... and the postcondition does not
    expect(result.reason).toContain("does not hold");
  });

  whenZ3("the `?1` obligation of the section 6.3 skeleton: `Le lo lo` under `x + 1 <= lo`", () => {
    // Context: lo : Int, h : Le (lo + 1) lo
    const depth = 2;
    const lo = at(0, depth);
    const context = makeContext(depth, [K.Int, K.Le(K.Add(lo, K.intLit(1n)), lo)]);
    const ob: Obligation = {
      id: "clamp-lo-lo",
      kind: "post",
      span: span(6, 15),
      context,
      hypotheses: [K.Le(K.Add(lo, K.intLit(1n)), lo)],
      goal: K.Le(lo, lo),
      atomNames: names(depth, ["lo", "h"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    const checked = checkClosed(context, ["lo", "h1"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
  });

  whenZ3("the section 6.4 clamp path certificate: `x + 1 <= lo` and `lo <= hi` give `x <= hi`", () => {
    // Context: x, lo, hi, h1 : Le (x + 1) lo, pre : Le lo hi
    const depth = 5;
    const x = at(0, depth);
    const lo = at(1, depth);
    const hi = at(2, depth);
    const context = makeContext(depth, [
      K.Int,
      K.Int,
      K.Int,
      K.Le(K.Add(x, K.intLit(1n)), lo),
      K.Le(lo, hi),
    ]);
    const ob: Obligation = {
      id: "clamp-path",
      kind: "post",
      span: span(6, 15),
      context,
      hypotheses: [K.Le(K.Add(x, K.intLit(1n)), lo), K.Le(lo, hi)],
      goal: K.Le(x, hi),
      atomNames: names(depth, ["x", "lo", "hi", "h1", "pre"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    // Rows: `x - lo <= -1`, `lo - hi <= 0`, `hi - x <= -1`; lambda = [1, 1, 1] leaves -2.
    expect(result.multipliers).toEqual([1n, 1n, 1n]);
    const hypTypes = kernelHypTypes(ob, K.Lt(hi, x));
    expect(K.checkFarkas({ hypTypes, coeffs: result.multipliers! }).ok).toBe(true);
    const checked = checkClosed(context, ["x", "lo", "hi", "h1", "pre"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });
});

// ---------------------------------------------------------------------------
// Other obligation shapes
// ---------------------------------------------------------------------------

describe("equalities and disjunctions", () => {
  whenZ3("a `===` goal is proven as two `Le` goals combined with `intEq`", () => {
    const depth = 3;
    const x = at(0, depth);
    const context = makeContext(depth, [K.Int, K.Le(K.Neg(x), K.intLit(0n)), K.Le(x, K.intLit(0n))]);
    const ob: Obligation = {
      id: "eq-zero",
      kind: "post",
      span: span(),
      context,
      hypotheses: [K.Le(K.Neg(x), K.intLit(0n)), K.Le(x, K.intLit(0n))],
      goal: K.Eq(K.Int, x, K.intLit(0n)),
      atomNames: names(depth, ["x", "h1", "h2"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    expect(K.formatTerm(result.proof!)).toContain("intEq");
    const checked = checkClosed(context, ["x", "h1", "h2"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });

  whenZ3("a `||` goal is proven by an `ifLe` split with one disjunct per branch", () => {
    const depth = 1;
    const x = at(0, depth);
    const disjunction = K.Sum(K.Le(x, K.intLit(0n)), K.Le(K.intLit(1n), x));
    const context = makeContext(depth, [K.Int]);
    const ob: Obligation = {
      id: "disjunction",
      kind: "post",
      span: span(),
      context,
      hypotheses: [],
      goal: disjunction,
      atomNames: names(depth, ["x"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    const text = K.formatTerm(result.proof!);
    expect(text).toContain("ifLe");
    expect(text).toContain("inl");
    expect(text).toContain("inr");
    const checked = checkClosed(context, ["x"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });

  whenZ3("a `!==` hypothesis is split into `<` and `>`", () => {
    const depth = 3;
    const n = at(0, depth);
    const context = makeContext(depth, [
      K.Int,
      K.Not(K.Eq(K.Int, n, K.intLit(0n))),
      K.Le(K.intLit(0n), n),
    ]);
    const ob: Obligation = {
      id: "disequality",
      kind: "post",
      span: span(),
      context,
      hypotheses: [K.Not(K.Eq(K.Int, n, K.intLit(0n))), K.Le(K.intLit(0n), n)],
      goal: K.Le(K.intLit(1n), n),
      atomNames: names(depth, ["n", "hneq", "h0"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    expect(K.formatTerm(result.proof!)).toContain("ifLe");
    const checked = checkClosed(context, ["n", "hneq", "h0"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });

  whenZ3("a `||` hypothesis is a `Sum`, eliminated with `case`", () => {
    const depth = 2;
    const x = at(0, depth);
    const disjunction = K.Sum(K.Le(x, K.intLit(0n)), K.Le(K.intLit(1n), x));
    const context = makeContext(depth, [K.Int, disjunction]);
    const ob: Obligation = {
      id: "sum-hypothesis",
      kind: "post",
      span: span(),
      context,
      hypotheses: [disjunction],
      goal: disjunction,
      atomNames: names(depth, ["x", "h"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    expect(K.formatTerm(result.proof!)).toContain("case");
    const checked = checkClosed(context, ["x", "h"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });
});

describe("range obligations", () => {
  whenZ3("`InRange x` and `x < 0` prove `InRange (-x)` (the `abs` range site)", () => {
    const depth = 3;
    const x = at(0, depth);
    const context = makeContext(depth, [K.Int, K.InRange(x), K.Lt(x, K.intLit(0n))]);
    const ob: Obligation = {
      id: "abs-range",
      kind: "range",
      span: span(6, 18),
      context,
      hypotheses: [K.InRange(x), K.Lt(x, K.intLit(0n))],
      goal: K.InRange(K.Neg(x)),
      atomNames: names(depth, ["x", "r_x", "h"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    const checked = checkClosed(context, ["x", "r_x", "h"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
    if (!checked.ok) throw new Error(K.formatKernelError(checked.error));
  });
});

// ---------------------------------------------------------------------------
// Not-proven outcomes
// ---------------------------------------------------------------------------

describe("not proven", () => {
  // x + y <= 1, 1 <= x + y, x <= y, y <= x  |-  false:  the negation is rationally
  // satisfiable (x = y = 1/2) but integer-infeasible, so no per-row tightening refutes it
  // and no Farkas certificate exists (section 11's smt-only case).
  const cpDepth = 6;
  const px = at(0, cpDepth);
  const py = at(1, cpDepth);
  const cpContext = makeContext(cpDepth, [
    K.Int,
    K.Int,
    K.Le(K.Add(px, py), K.intLit(1n)),
    K.Le(K.intLit(1n), K.Add(px, py)),
    K.Le(px, py),
    K.Le(py, px),
  ]);
  const cuttingPlanes: Obligation = {
    id: "cutting-planes",
    kind: "post",
    span: span(),
    context: cpContext,
    hypotheses: [
      K.Le(K.Add(px, py), K.intLit(1n)),
      K.Le(K.intLit(1n), K.Add(px, py)),
      K.Le(px, py),
      K.Le(py, px),
    ],
    goal: K.Le(K.intLit(1n), K.intLit(0n)),
    atomNames: names(cpDepth, ["x", "y", "h0", "h1", "h2", "h3"]),
  };

  whenZ3("a valid obligation with no Farkas certificate is `smt-only`", () => {
    const result = C.certify(env, cuttingPlanes);
    expect(result.status).toBe("smt-only");
    expect(result.proof).toBeUndefined();
    expect(result.reason).toContain("no Farkas certificate");
  });

  whenZ3("a tiny timeout yields not proven, never certified", () => {
    const result = C.certify(env, cuttingPlanes, { timeoutMs: 1 });
    expect(result.status).not.toBe("certified");
    expect(result.proof).toBeUndefined();
    expect(result.reason!.length).toBeGreaterThan(0);
  });

  whenZ3("an obligation with an unencodable hypothesis is not reported smt-only", () => {
    const opaque = K.Eq(K.Unit, K.tt, K.tt);
    const ob: Obligation = {
      id: "opaque",
      kind: "post",
      span: span(),
      hypotheses: [opaque],
      goal: K.Le(K.intLit(1n), K.intLit(0n)),
      context: makeContext(1, [opaque]),
      atomNames: {},
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("failed");
    expect(result.reason).toContain("outside the SMT encoding");
  });

  whenZ3("missing proof terms are reported instead of guessed", () => {
    const depth = 1;
    const x = at(0, depth);
    const ob: Obligation = {
      id: "no-proofs",
      kind: "post",
      span: span(),
      // Two hypotheses that are *not* binders of the one-binder context, and no `proofs`.
      context: makeContext(depth, [K.Int]),
      hypotheses: [K.Le(x, K.intLit(0n)), K.Le(K.intLit(1n), x)],
      goal: K.Le(K.intLit(1n), K.intLit(0n)),
      atomNames: names(depth, ["x"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("failed");
    expect(result.reason).toContain("does not say where the proof");
  });

  whenZ3("explicit `proofs` name hypotheses that are not context binders", () => {
    const depth = 3;
    const x = at(0, depth);
    const context = makeContext(depth, [K.Int, K.Le(x, K.intLit(0n)), K.Le(K.intLit(1n), x)]);
    const ob: Obligation = {
      id: "derived-hypotheses",
      kind: "post",
      span: span(),
      context,
      // The same propositions, but proved by the context binders the caller chose.
      hypotheses: [K.Le(x, K.intLit(0n)), K.Le(K.intLit(1n), x)],
      proofs: [at(1, depth), at(2, depth)],
      goal: K.Le(K.intLit(1n), K.intLit(0n)),
      atomNames: names(depth, ["x", "h1", "h2"]),
    };
    const result = C.certify(env, ob);
    expect(result.status).toBe("certified");
    const checked = checkClosed(context, ["x", "h1", "h2"], result.proof!, ob.goal);
    expect(checked.ok).toBe(true);
  });

  whenZ3("the context survives a failure: a later obligation still certifies", () => {
    expect(C.certify(env, cuttingPlanes).status).toBe("smt-only");
    expect(C.certify(env, clampNoPreObligation).status).toBe("failed");
    const after = C.certify(env, boundsObligation);
    expect(after.status).toBe("certified");
  });

  whenZ3("a malformed obligation is rejected by the kernel self-check, not certified", () => {
    // `Le Unit Unit` is not a proposition: with a (empty) context, `certify` finds a
    // "certificate" for the nonsense rows and then the kernel refuses the proof.
    const broken: Obligation = {
      id: "broken",
      kind: "post",
      span: span(),
      context: [],
      hypotheses: [],
      goal: K.Le(K.Unit, K.Unit),
    };
    const result = C.certify(env, broken);
    expect(result.status).toBe("failed");
    expect(result.proof).toBeUndefined();
    expect(result.reason).toContain("kernel rejected");
  });

  test("an obligation with a nonsensical goal still returns a result, never throws", () => {
    const broken: Obligation = {
      id: "broken-bare",
      kind: "post",
      span: span(),
      hypotheses: [],
      goal: K.Le(K.Unit, K.Unit),
    };
    const result = C.certify(env, broken);
    expect(["certified", "smt-only", "failed"]).toContain(result.status);
  });
});
