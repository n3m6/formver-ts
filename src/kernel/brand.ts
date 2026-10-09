/**
 * The environment brand: the kernel's answer to "is this environment really ours?".
 *
 * `Env` is a structural type, so without a brand untrusted code could fabricate one — or
 * hand in a mutated copy — and get declarations (including `axiom`s) accepted without ever
 * passing through `addDecl`, which specification section 6.1.5 says is the only way to
 * insert.  `emptyEnv` and `addDecl` brand every environment they build; the public checking
 * entry points reject anything unbranded.
 *
 * This lives in its own module so that `check.ts`/`conv.ts`/`quote.ts` can consult the brand
 * without importing `env.ts` (which imports them) at runtime.
 */
import { kernelError, type KernelError } from "./errors";

const knownEnvs = new WeakSet<object>();

/** Freeze an environment and record it as kernel-built. */
export function brandEnv<T extends object>(env: T): T {
  Object.freeze(env);
  knownEnvs.add(env);
  return env;
}

export function isKnownEnv(env: object): boolean {
  return knownEnvs.has(env);
}

export function unknownEnvError(): KernelError {
  return kernelError(
    "unknown-environment",
    "this environment was not built by emptyEnv/addDecl; addDecl is the only way to insert a declaration",
    {},
  );
}
