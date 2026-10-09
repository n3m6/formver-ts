/**
 * `src/vc/smtlib.ts`: atom tables, the two query shapes, the model decoder — and the one
 * hard rule of section 3.3, that `div` and `mod` are never emitted.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import * as L from "../../src/vc/linear";
import * as S from "../../src/vc/smtlib";
import * as Z from "../../src/vc/z3";
import { env, whenZ3 } from "./helpers";

const depth = 2;
const x = K.varTerm(1);
const y = K.varTerm(0);

const le = (lhs: K.Term, rhs: K.Term): K.Term => K.Le(lhs, rhs);
const proposition = (term: K.Term): L.Proposition => L.propositionOfTerm(env, depth, term);

describe("AtomTable", () => {
  test("names atoms a0, a1, … in first-seen order and interns idempotently", () => {
    const atoms = new S.AtomTable(env, depth);
    const first = atoms.intern("Var(0)", K.vvar(0));
    const second = atoms.intern("Var(1)", K.vvar(1));
    expect(first.name).toBe("a0");
    expect(second.name).toBe("a1");
    expect(atoms.intern("Var(0)").name).toBe("a0");
    expect(atoms.size).toBe(2);
    expect(atoms.declarations()).toEqual(["(declare-const a0 Int)", "(declare-const a1 Int)"]);
    // Quoted in a context of `depth` binders: level 0 is the innermost index.
    expect(K.formatTerm(first.representative!)).toBe("?1");
  });
});

describe("printing", () => {
  test("a linear form becomes a polynomial over the atom names", () => {
    const atoms = new S.AtomTable(env, depth);
    const form = L.formOfTerm(env, K.Add(K.MulConst(K.intLit(3n), x), K.Neg(y)), depth);
    expect(S.printForm(atoms, form)).toBe("(+ 0 (* 3 a0) (- a1))");
    const justX = L.formOfTerm(env, x, depth);
    expect(S.printForm(atoms, justX)).toBe("a0");
    expect(S.printForm(atoms, L.formOfTerm(env, K.Neg(x), depth))).toBe("(- a0)");
    const constant = L.formOfTerm(env, K.intLit(-4n), depth);
    expect(S.printForm(atoms, constant)).toBe("-4");
  });

  test("a row is printed as `<=` over a fresh atom table", () => {
    const atoms = new S.AtomTable(env, depth);
    const row = L.rowOfLeTerms(env, depth, K.Add(K.MulConst(K.intLit(2n), x), y), K.intLit(3n));
    // 2x + y <= 3
    expect(S.printRow(atoms, row)).toBe("(<= (+ 0 (* 2 a0) a1) 3)");
  });

  test("the obligation script asserts hypotheses and the negated goal", () => {
    const query = S.printObligation({
      env,
      depth,
      hypotheses: [proposition(le(K.intLit(0n), x))],
      goal: proposition(le(K.intLit(1n), x)),
    });
    expect(query.complete).toBe(true);
    expect(query.negatedGoal).toBe("(not (<= 1 a0))");
    expect(query.script).toContain("(declare-const a0 Int)");
    expect(query.script).toContain("(assert (<= 0 a0))");
    expect(query.script).toContain("(assert (not (<= 1 a0)))");
    expect(query.script).toContain("(check-sat)");
    expect(query.script.startsWith("(push)")).toBe(true);
    expect(query.script.endsWith("(pop)")).toBe(true);
    expect(query.script).not.toContain("get-model");
  });

  test("an unprintable proposition makes the query incomplete", () => {
    const opaque = proposition(K.Eq(K.Unit, K.tt, K.tt)); // Eq over Unit, not Int
    const query = S.printObligation({ env, depth, hypotheses: [opaque], goal: proposition(le(x, y)) });
    expect(query.complete).toBe(false);
  });

  test("the certificate query asks for non-negative integer multipliers", () => {
    const rows = [
      { row: L.tightenRow({ a: { k0: 2n }, b: 1n }), atoms: new Map<string, L.Atom>() },
      { row: L.tightenRow({ a: { k0: -2n }, b: -1n }), atoms: new Map<string, L.Atom>() },
    ];
    const probe = S.printCertificateQuery({ env, depth, rows }, "sat");
    expect(probe.multipliers).toEqual(["l0", "l1"]);
    expect(probe.script).toContain("(declare-const l0 Int)");
    expect(probe.script).toContain("(assert (>= l0 0))");
    expect(probe.script).toContain("(assert (< (+ 0 (* 0 l0) (* -1 l1)) 0))");
    expect(probe.script).toContain("(check-sat)");
    expect(probe.script).not.toContain("get-value");
    const values = S.printCertificateQuery({ env, depth, rows }, "values");
    expect(values.script).toContain("(get-value (l0 l1))");
  });

  test("never emits `div` or `mod`, even for a division atom", () => {
    // `divFloor x 2` is an opaque atom: its value is not linear, and the *encoding* is a
    // constant, not SMT-LIB division (whose rounding differs from JavaScript's).
    const quotient = K.DivFloor(x, K.intLit(2n));
    const query = S.printObligation({
      env,
      depth,
      hypotheses: [proposition(le(K.intLit(0n), quotient))],
      goal: proposition(le(K.intLit(0n), quotient)),
    });
    expect(query.complete).toBe(true);
    expect(/\bdiv\b|\bmod\b|divFloor|divTrunc/.test(query.script)).toBe(false);
    expect(query.atoms.size).toBe(1);
    expect(K.formatTerm(query.atoms.entries()[0]!.representative!)).toContain("divFloor");
    const certificate = S.printCertificateQuery(
      { env, depth, rows: [{ row: L.tightenRow(L.rowOfLeTerms(env, depth, K.intLit(0n), quotient)), atoms: new Map() }] },
      "values",
    );
    expect(/\bdiv\b|\bmod\b/.test(certificate.script)).toBe(false);
  });
});

describe("decoding", () => {
  test("parseVerdict finds the check-sat answer, not a model line", () => {
    expect(S.parseVerdict("sat")).toBe("sat");
    expect(S.parseVerdict("unsat")).toBe("unsat");
    expect(S.parseVerdict("unknown")).toBe("unknown");
    expect(
      S.parseVerdict("sat\n(\n  (define-fun a0 () Int\n    3)\n)"),
    ).toBe("sat");
    expect(S.parseVerdict("(error \"boom\")")).toBeUndefined();
  });

  test("decodeModel reads numerals and `(- n)` values", () => {
    const model = S.decodeModel(`sat
(
  (define-fun a1 () Int
    (- 2))
  (define-fun a0 () Int
    3)
)`);
    expect(model).toEqual({ a0: "3", a1: "-2" });
    expect(S.decodeModel("(define-fun f ((z Int)) Int 0)")).toEqual({});
  });

  test("decodeValues reads the multiplier vector by name", () => {
    expect(S.decodeValues("sat\n((l0 0)\n (l1 1)\n (l2 1))", ["l0", "l1", "l2"])).toEqual({
      l0: "0",
      l1: "1",
      l2: "1",
    });
    expect(S.decodeValues("sat", ["l0"])).toBeUndefined();
  });
});

describe("end to end", () => {
  whenZ3("a printed obligation runs unchanged through the binding", () => {
    const query = S.printObligation({
      env,
      depth,
      hypotheses: [proposition(le(K.intLit(0n), x)), proposition(le(K.Add(x, K.intLit(1n)), y))],
      goal: proposition(le(x, y)),
    });
    const reply = Z.evalScript(query.script, { timeoutMs: 2000 });
    expect(reply.ok).toBe(true);
    expect(S.parseVerdict(reply.output)).toBe("unsat");
    const model = S.printObligation({
      env,
      depth,
      hypotheses: [],
      goal: proposition(le(K.intLit(1n), K.intLit(0n))),
      model: true,
    });
    const withModel = Z.evalScript(model.script, { timeoutMs: 2000 });
    expect(S.parseVerdict(withModel.output)).toBe("sat");
    expect(S.decodeModel(withModel.output)).toBeDefined();
  });
});
