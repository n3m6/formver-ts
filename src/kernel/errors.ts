/**
 * Structured kernel errors and the kernel-local `Result` type.
 *
 * The kernel never throws `KernelError`: every fallible operation returns a `Result`.
 * `KernelInternalError` is different: it is thrown for conditions that mean a bug in the
 * trusted kernel itself (a malformed primitive type, a value that cannot be applied, an
 * out-of-scope variable). The public entry points catch it and turn it into a
 * `reason: "internal"` error.
 */
import type { PrimOp, Term } from "./term";

/** Machine-readable reason tag. Milestone 3 extends this union, it does not rename it. */
export type KernelErrorReason =
  | "unbound-variable"
  | "unbound-constant"
  | "unknown-prim"
  | "prim-arity"
  | "not-a-function"
  | "not-a-sigma"
  | "not-a-type"
  | "type-mismatch"
  /** Milestone 3: a built-in argument that must be a positive integer literal is not. */
  | "prim-not-literal"
  | "duplicate-decl"
  | "ill-typed-decl"
  | "invalid-axiom"
  | "invalid-external"
  | "farkas-shape"
  | "farkas-negative-coefficient"
  | "farkas-not-a-le-hypothesis"
  | "farkas-unimplemented"
  | "farkas-invalid"
  | "internal";

export interface KernelError {
  readonly reason: KernelErrorReason;
  /** Human-readable message, suitable for a diagnostic. */
  readonly message: string;
  /** The offending term, when one can be named. */
  readonly term?: Term;
  /** For mismatch errors: the expected type. */
  readonly expected?: Term;
  /** For mismatch errors: the type that was inferred. */
  readonly actual?: Term;
  /** For declaration errors: the declaration name. */
  readonly name?: string;
  /** For primitive errors: the op tag. */
  readonly op?: PrimOp;
  /** The lower-level kernel error this one elaborates. */
  readonly cause?: KernelError;
}

export type Result<T, E = KernelError> =
  | { readonly ok: true; readonly value: T }
  | { readonly ok: false; readonly error: E };

export const ok = <T>(value: T): Result<T, never> => ({ ok: true, value });

export const err = <E>(error: E): Result<never, E> => ({ ok: false, error });

export function kernelError(
  reason: KernelErrorReason,
  message: string,
  extra?: Omit<KernelError, "reason" | "message">,
): KernelError {
  return extra === undefined ? { reason, message } : { reason, message, ...extra };
}

/** A bug in the trusted kernel itself, not a rejected user term. */
export class KernelInternalError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "KernelInternalError";
  }
}

/** Turns an unknown thrown value into a `reason: "internal"` kernel error. */
export function internalError(cause: unknown): KernelError {
  const message = cause instanceof Error ? cause.message : String(cause);
  return kernelError("internal", `internal kernel error: ${message}`);
}

export function formatKernelError(error: KernelError): string {
  const parts = [`error[${error.reason}]: ${error.message}`];
  if (error.cause !== undefined) parts.push(`  caused by: ${formatKernelError(error.cause)}`);
  return parts.join("\n");
}
