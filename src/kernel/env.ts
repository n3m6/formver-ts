/**
 * The global environment: name -> declaration, and the only way to insert one.
 *
 * A declaration is one of the three kinds of specification section 6.1.5:
 *
 *   def       a checked definition; `opaque` disables delta unfolding (used for `fixWf`)
 *   axiom     reserved for statements taken on trust; the MVP must end with zero of these
 *   external  another file's function, with the content hash it was certified under
 *
 * `addDecl` type-checks first and returns a *new* environment; it never mutates the one it
 * was given. `emptyEnv()` seeds the prelude through `addDecl` as well, so the kernel
 * checks its own built-ins and there is no back door into the environment.
 */
import { builtinDecls } from "./builtins";
import { checkType, isTypeTerm } from "./check";
import { err, kernelError, KernelInternalError, ok, type KernelError, type Result } from "./errors";
import type { Term } from "./term";

export interface DefDecl {
  readonly kind: "def";
  readonly name: string;
  readonly type: Term;
  readonly value: Term;
  /** Opaque definitions are not unfolded by delta; conversion stops at their name. */
  readonly opaque?: boolean;
}

export interface AxiomDecl {
  readonly kind: "axiom";
  readonly name: string;
  readonly type: Term;
  /** Why this statement is taken on trust. Reported by `axiomsUsed`. */
  readonly reason: string;
}

export interface ExternalDecl {
  readonly kind: "external";
  readonly name: string;
  readonly type: Term;
  /** The file the declaration came from and the hash of its contents when certified. */
  readonly source: { readonly file: string; readonly hash: string };
}

export type Decl = DefDecl | AxiomDecl | ExternalDecl;

export interface Env {
  readonly decls: ReadonlyMap<string, Decl>;
  /** Declaration names in insertion order; makes reporting deterministic. */
  readonly order: readonly string[];
}

/**
 * The starting environment: the built-in definitions of specification section 6.1.3,
 * inserted through `addDecl` so that they are kernel-checked. Zero axioms.
 */
export function emptyEnv(): Env {
  let env: Env = { decls: new Map(), order: [] };
  for (const decl of builtinDecls()) {
    const added = addDecl(env, decl);
    if (!added.ok) {
      throw new KernelInternalError(
        `the built-in definition ${decl.name} failed to type-check: ${added.error.message}`,
      );
    }
    env = added.value;
  }
  return env;
}

/**
 * The only way to insert a declaration. Checks the declared type and, for a definition,
 * the definition itself; on any failure the environment is returned unchanged (as an
 * error result, with no new environment to use).
 */
export function addDecl(env: Env, decl: Decl): Result<Env, KernelError> {
  if (env.decls.has(decl.name)) {
    return err(
      kernelError("duplicate-decl", `the name ${decl.name} is already declared`, { name: decl.name }),
    );
  }
  const typeLevel = isTypeTerm(env, decl.type);
  if (!typeLevel.ok) {
    return err(
      kernelError("ill-typed-decl", `the declared type of ${decl.name} is not a well-formed type`, {
        name: decl.name,
        cause: typeLevel.error,
      }),
    );
  }
  if (decl.kind === "def") {
    const checked = checkType(env, decl.value, decl.type);
    if (!checked.ok) {
      return err(
        kernelError("ill-typed-decl", `the definition of ${decl.name} does not check against its type`, {
          name: decl.name,
          cause: checked.error,
        }),
      );
    }
  } else if (decl.kind === "axiom") {
    if (decl.reason.trim() === "") {
      return err(
        kernelError("invalid-axiom", `the axiom ${decl.name} must record a reason`, { name: decl.name }),
      );
    }
  } else if (decl.source.file.trim() === "" || decl.source.hash.trim() === "") {
    return err(
      kernelError(
        "invalid-external",
        `the external declaration ${decl.name} needs both a source file and a content hash`,
        { name: decl.name },
      ),
    );
  }
  const decls = new Map(env.decls);
  decls.set(decl.name, decl);
  return ok({ decls, order: [...env.order, decl.name] });
}

export function lookupDecl(env: Env, name: string): Decl | undefined {
  return env.decls.get(name);
}

/** Names of declarations of kind `axiom`, in insertion order. Must be `[]` for the MVP. */
export function axiomsUsed(env: Env): string[] {
  return env.order.filter((name) => env.decls.get(name)?.kind === "axiom");
}

/** External declarations, in insertion order. */
export function externalsUsed(env: Env): { name: string; file: string; hash: string }[] {
  const out: { name: string; file: string; hash: string }[] = [];
  for (const name of env.order) {
    const decl = env.decls.get(name);
    if (decl !== undefined && decl.kind === "external") {
      out.push({ name: decl.name, file: decl.source.file, hash: decl.source.hash });
    }
  }
  return out;
}
