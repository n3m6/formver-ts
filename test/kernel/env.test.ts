/**
 * The environment: three declaration kinds, `addDecl` as the only insertion path, and the
 * zero-axiom prelude.
 */
import { describe, expect, test } from "bun:test";
import * as K from "../../src/kernel/index";
import { endoId, expectErr, expectOk } from "./helpers";

const unitToUnit: K.Term = K.pi("_", K.Unit, K.Unit);

describe("emptyEnv", () => {
  const env = K.emptyEnv();

  test("uses zero axioms", () => {
    expect(K.axiomsUsed(env)).toEqual([]);
    expect(K.externalsUsed(env)).toEqual([]);
  });

  test("preloads the built-ins as definitions", () => {
    for (const name of [K.AND_NAME, K.NOT_NAME]) {
      const decl = K.lookupDecl(env, name);
      expect(decl?.kind).toBe("def");
    }
    expect(K.lookupDecl(env, "Empty")).toBeUndefined();
  });

  test("its definitions are checked, not axiomatized", () => {
    const andDecl = K.lookupDecl(env, K.AND_NAME);
    expect(andDecl?.kind).toBe("def");
    if (andDecl?.kind !== "def") return;
    expect(K.checkType(env, andDecl.value, andDecl.type).ok).toBe(true);
  });

  test("is a fresh environment each time", () => {
    const a = K.emptyEnv();
    const b = expectOk(
      K.addDecl(a, { kind: "def", name: "extra", type: unitToUnit, value: endoId }),
    );
    expect(K.lookupDecl(a, "extra")).toBeUndefined();
    expect(K.lookupDecl(b, "extra")?.kind).toBe("def");
    expect(K.emptyEnv().order).toEqual(a.order);
  });
});

describe("addDecl", () => {
  const env = K.emptyEnv();

  test("inserts a well-typed definition and returns a new environment", () => {
    const next = expectOk(K.addDecl(env, { kind: "def", name: "myId", type: unitToUnit, value: endoId }));
    expect(K.lookupDecl(env, "myId")).toBeUndefined();
    expect(K.lookupDecl(next, "myId")?.kind).toBe("def");
    expect(next.order).toEqual([...env.order, "myId"]);
    expect(K.axiomsUsed(next)).toEqual([]);
  });

  test("rejects an ill-typed definition and does not mutate the environment", () => {
    const error = expectErr(K.addDecl(env, { kind: "def", name: "bad", type: unitToUnit, value: K.tt }));
    expect(error.reason).toBe("ill-typed-decl");
    expect(error.cause?.reason).toBe("type-mismatch");
    expect(K.lookupDecl(env, "bad")).toBeUndefined();
    expect(env.order).not.toContain("bad");
    // The rejected name is still free afterwards.
    expect(K.addDecl(env, { kind: "def", name: "bad", type: unitToUnit, value: endoId }).ok).toBe(true);
  });

  test("rejects a declaration whose type is not a type", () => {
    const error = expectErr(K.addDecl(env, { kind: "def", name: "weird", type: K.tt, value: K.tt }));
    expect(error.reason).toBe("ill-typed-decl");
    expect(K.lookupDecl(env, "weird")).toBeUndefined();
  });

  test("rejects a declaration with a free variable or an unknown constant", () => {
    const free = expectErr(K.addDecl(env, { kind: "def", name: "free", type: unitToUnit, value: K.varTerm(0) }));
    expect(free.reason).toBe("ill-typed-decl");
    expect(free.cause?.reason).toBe("unbound-variable");
    const unknown = expectErr(
      K.addDecl(env, { kind: "def", name: "unk", type: unitToUnit, value: K.constTerm("other") }),
    );
    expect(unknown.reason).toBe("ill-typed-decl");
    expect(unknown.cause?.reason).toBe("unbound-constant");
  });

  test("rejects duplicate names", () => {
    const one = expectOk(K.addDecl(env, { kind: "def", name: "dup", type: unitToUnit, value: endoId }));
    expect(expectErr(K.addDecl(one, { kind: "def", name: "dup", type: unitToUnit, value: endoId })).reason).toBe(
      "duplicate-decl",
    );
    expect(expectErr(K.addDecl(one, { kind: "axiom", name: "dup", type: unitToUnit, reason: "x" })).reason).toBe(
      "duplicate-decl",
    );
  });

  test("a definition can use earlier declarations", () => {
    const one = expectOk(K.addDecl(env, { kind: "def", name: "base", type: unitToUnit, value: endoId }));
    const two = expectOk(
      K.addDecl(one, { kind: "def", name: "derived", type: unitToUnit, value: K.constTerm("base") }),
    );
    expect(K.isConvertible(two, K.constTerm("derived"), endoId)).toBe(true);
  });

  test("reports axioms but never requires them", () => {
    const withAxiom = expectOk(
      K.addDecl(env, { kind: "axiom", name: "trusted", type: unitToUnit, reason: "test fixture" }),
    );
    expect(K.axiomsUsed(withAxiom)).toEqual(["trusted"]);
    expect(K.axiomsUsed(env)).toEqual([]);
    expect(expectErr(K.addDecl(env, { kind: "axiom", name: "why", type: unitToUnit, reason: "  " })).reason).toBe(
      "invalid-axiom",
    );
  });

  test("records external declarations with their file and hash", () => {
    const withExternal = expectOk(
      K.addDecl(env, {
        kind: "external",
        name: "imported",
        type: unitToUnit,
        source: { file: "/tmp/other.ts", hash: "deadbeef" },
      }),
    );
    expect(K.externalsUsed(withExternal)).toEqual([
      { name: "imported", file: "/tmp/other.ts", hash: "deadbeef" },
    ]);
    expect(K.axiomsUsed(withExternal)).toEqual([]);
    expect(K.isConvertible(withExternal, K.constTerm("imported"), endoId)).toBe(false);
    expect(
      expectErr(
        K.addDecl(env, {
          kind: "external",
          name: "broken",
          type: unitToUnit,
          source: { file: "", hash: "x" },
        }),
      ).reason,
    ).toBe("invalid-external");
    expect(
      expectErr(
        K.addDecl(env, {
          kind: "external",
          name: "broken2",
          type: unitToUnit,
          source: { file: "x.ts", hash: "" },
        }),
      ).reason,
    ).toBe("invalid-external");
  });

  test("an opaque definition is still type-checked", () => {
    const good = expectOk(
      K.addDecl(env, { kind: "def", name: "opaqueGood", type: unitToUnit, value: endoId, opaque: true }),
    );
    expect(K.lookupDecl(good, "opaqueGood")).toEqual({
      kind: "def",
      name: "opaqueGood",
      type: unitToUnit,
      value: endoId,
      opaque: true,
    });
    expect(
      expectErr(K.addDecl(env, { kind: "def", name: "opaqueBad", type: unitToUnit, value: K.tt, opaque: true })).reason,
    ).toBe("ill-typed-decl");
  });

  test("lookupDecl returns undefined for unknown names", () => {
    expect(K.lookupDecl(env, "nope")).toBeUndefined();
  });
});
