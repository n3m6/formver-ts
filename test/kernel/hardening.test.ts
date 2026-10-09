/**
 * Kernel hardening tests: the invariants an adversarial audit tried to break.
 *
 *   - universe levels are non-negative safe integers, so `Type 2^53 : Type 2^53`,
 *     `Type 1.5 : Type 2.5` and `Type -Infinity : Type -Infinity` are rejected;
 *   - an `Env` that `emptyEnv`/`addDecl` did not build is refused (specification 6.1.5:
 *     `addDecl` is the only way to insert), and its declaration table cannot be mutated;
 *   - a malformed term node is a located `not-a-term` error, never a crash.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";

const env = K.emptyEnv();

describe("universe levels", () => {
  const badLevels = [2 ** 53, 2 ** 53 - 1, -1, 1.5, Number.NaN, Number.POSITIVE_INFINITY, Number.NEGATIVE_INFINITY];

  for (const level of badLevels) {
    test(`Type ${level} is rejected`, () => {
      const sort = K.sort(level);
      const checked = K.isTypeTerm(env, sort);
      expect(checked.ok).toBe(false);
      expect(K.inferType(env, sort).ok).toBe(false);
      // `Type l : Type l` must not be derivable for such an `l`.
      expect(K.checkType(env, sort, sort).ok).toBe(false);
    });
  }

  test("valid levels still work", () => {
    expect(K.isTypeTerm(env, K.sort(0)).ok).toBe(true);
    const inferred = K.inferType(env, K.sort(0));
    expect(inferred.ok).toBe(true);
    if (inferred.ok) expect(K.formatTerm(inferred.value)).toBe(K.formatTerm(K.sort(1)));
    expect(K.checkType(env, K.sort(1), K.sort(2)).ok).toBe(true);
    expect(K.checkType(env, K.sort(1), K.sort(1)).ok).toBe(false);
  });
});

describe("environment branding", () => {
  test("a fabricated environment is refused by every checking entry point", () => {
    const fake = { decls: new Map(), order: [] } as unknown as K.Env;
    const magic: K.Decl = { kind: "axiom", name: "magic", type: K.Empty, reason: "forged" };
    expect(K.addDecl(fake, magic).ok).toBe(false);
    expect(K.inferType(fake, K.tt).ok).toBe(false);
    expect(K.checkType(fake, K.tt, K.Unit).ok).toBe(false);
    expect(K.isTypeTerm(fake, K.Unit).ok).toBe(false);
    expect(K.isConvertible(fake, K.tt, K.tt)).toBe(false);
    expect(K.axiomsUsed(K.emptyEnv())).toEqual([]);
  });

  test("the declaration table of a real environment cannot be mutated", () => {
    const table = env.decls as Map<string, K.Decl>;
    expect(() =>
      table.set("magic", { kind: "axiom", name: "magic", type: K.Empty, reason: "forged" }),
    ).toThrow();
    expect(() => table.delete("Unit")).toThrow();
    expect(() => table.clear()).toThrow();
    expect(K.axiomsUsed(env)).toEqual([]);
  });

  test("addDecl still works and reports ill-typed declarations", () => {
    const good = K.addDecl(env, { kind: "def", name: "myId", type: K.pi("_", K.Int, K.Int), value: K.lam("x", K.Int, K.varTerm(0)) });
    expect(good.ok).toBe(true);
    const bad = K.addDecl(env, { kind: "def", name: "bad", type: K.Empty, value: K.tt });
    expect(bad.ok).toBe(false);
    const axiom = K.addDecl(env, { kind: "axiom", name: "trust", type: K.Empty, reason: "why" });
    expect(axiom.ok).toBe(true);
    if (axiom.ok) expect(K.axiomsUsed(axiom.value)).toEqual(["trust"]);
  });
});

describe("malformed terms", () => {
  test("an unrecognized term node is a located error, not a crash", () => {
    const nonsense = { tag: "Nonsense" } as unknown as K.Term;
    const inferred = K.inferType(env, nonsense);
    expect(inferred.ok).toBe(false);
    if (!inferred.ok) expect(inferred.error.reason).toBe("not-a-term");
    expect(K.checkType(env, nonsense, K.Int).ok).toBe(false);
  });

  test("a term with a missing child is a located error, not a crash", () => {
    const broken = { tag: "App", fn: { tag: "Lam", name: "x", domain: K.Int } } as unknown as K.Term;
    expect(K.inferType(env, broken).ok).toBe(false);
  });
});
