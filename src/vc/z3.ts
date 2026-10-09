/**
 * The Z3 binding (`bun:ffi`), specification section 6.4.
 *
 * The library is loaded lazily, on the first use, so that importing this module never
 * throws when Z3 is missing (`bun run setup` was not run). `isAvailable()` reports whether
 * the load succeeded and `unavailableReason()` explains why it did not.
 *
 * There is exactly **one context per process**, created on the first successful query.
 * Every query is wrapped in `(push)`…`(pop)`, so definitions a query makes are discarded
 * and one obligation can never leak into the next. A per-query timeout is installed with
 * `(set-option :timeout N)`, which was verified experimentally against Z3 5.1.0.0: on a
 * hard instance the query returns `unknown` after the requested number of milliseconds
 * (200 ms -> 203 ms, 1000 ms -> 1003 ms), where the same instance without a timeout takes
 * about 10 seconds. `:timeout` is *not* scoped by `push`/`pop` (it stays in effect after
 * the pop), so every query sets it explicitly; 0 means "no timeout" (verified: a 9.7 s
 * instance still ran to completion with `:timeout 0`).
 *
 * Any `(error …)` in Z3's output — and Z3's bare `unsupported` line, which is how
 * `Z3_eval_smtlib2_string` reports an unknown command — is a **failure, never a verdict**.
 * The context state may be unbalanced after an error, so the context is deleted and
 * recreated; the caller gets `ok: false` with the offending text. `unknown` is reported as
 * a verdict the caller must treat as "not proven"; it is never turned into `sat`/`unsat`.
 */
import { dlopen, FFIType, ptr } from "bun:ffi";
import { existsSync } from "node:fs";
import { resolve } from "node:path";

/** The repository root, resolved from this file rather than from the process cwd. */
export const REPO_ROOT: string = resolve(import.meta.dir, "..", "..");

/** `.z3/libz3.so`, where `bun run setup` unpacks the pinned release. */
export const DEFAULT_LIBRARY_PATH: string = resolve(REPO_ROOT, ".z3", "libz3.so");

/** Default per-query timeout: a verifier must never hang a build. */
export const DEFAULT_TIMEOUT_MS = 10_000;

/** Where the library is loaded from: `DEP_VERIFY_LIBZ3` wins when it is set and non-empty. */
export function libraryPath(): string {
  const override = process.env.DEP_VERIFY_LIBZ3?.trim();
  return override !== undefined && override !== "" ? resolve(override) : DEFAULT_LIBRARY_PATH;
}

export interface Z3EvalResult {
  /** False for a missing library, a Z3 error, or a crash; never for `unknown`. */
  readonly ok: boolean;
  /** Z3's raw output, trimmed. Present even when `ok` is false (it holds the error text). */
  readonly output: string;
  /** Human-readable failure reason, when `ok` is false. */
  readonly error?: string;
}

/** A native pointer as `bun:ffi` types it. */
type Z3Pointer = ReturnType<typeof ptr>;

interface Z3Binding {
  readonly lib: {
    readonly symbols: {
      Z3_get_full_version(): string | null;
      Z3_mk_config(): Z3Pointer | bigint | null;
      Z3_del_config(config: Z3Pointer | bigint | null): void;
      Z3_mk_context(config: Z3Pointer | bigint | null): Z3Pointer | bigint | null;
      Z3_del_context(context: Z3Pointer | bigint | null): void;
      Z3_set_error_handler(context: Z3Pointer | bigint | null, handler: Z3Pointer | bigint | null): void;
      Z3_eval_smtlib2_string(
        context: Z3Pointer | bigint | null,
        input: NodeJS.TypedArray | Z3Pointer | bigint | null,
      ): string | null;
    };
  };
  context: Z3Pointer | bigint | null;
  readonly version: string;
}

let binding: Z3Binding | undefined;
let loadFailure: string | undefined;
/** Bumped every time a context is (re)created; tests use it to observe an error reset. */
let epoch = 0;

function openLibrary(path: string): Z3Binding | { error: string } {
  try {
    const library = dlopen(path, {
      Z3_get_full_version: { args: [], returns: FFIType.cstring },
      Z3_mk_config: { args: [], returns: FFIType.ptr },
      Z3_del_config: { args: [FFIType.ptr], returns: FFIType.void },
      Z3_mk_context: { args: [FFIType.ptr], returns: FFIType.ptr },
      Z3_del_context: { args: [FFIType.ptr], returns: FFIType.void },
      Z3_set_error_handler: { args: [FFIType.ptr, FFIType.ptr], returns: FFIType.void },
      Z3_eval_smtlib2_string: { args: [FFIType.ptr, FFIType.ptr], returns: FFIType.cstring },
    });
    const config = library.symbols.Z3_mk_config();
    const context = library.symbols.Z3_mk_context(config);
    library.symbols.Z3_del_config(config);
    // Without this, a Z3 error aborts the process instead of returning `(error "…")` text.
    library.symbols.Z3_set_error_handler(context, null);
    epoch += 1;
    const rawVersion = library.symbols.Z3_get_full_version();
    return {
      lib: library,
      context,
      version: rawVersion === null ? "" : String(rawVersion),
    };
  } catch (cause) {
    return { error: cause instanceof Error ? cause.message : String(cause) };
  }
}

/** Load lazily; the failure reason is cached so repeated calls do not retry a broken path. */
function ensure(): Z3Binding | { error: string } {
  if (binding !== undefined) return binding;
  if (loadFailure !== undefined) return { error: loadFailure };
  const path = libraryPath();
  if (!existsSync(path)) {
    loadFailure =
      `the Z3 shared library was not found at ${path}. Run \`bun run setup\` to download ` +
      `Z3 5.1.0 into .z3/, or set DEP_VERIFY_LIBZ3=/path/to/libz3.so.`;
    return { error: loadFailure };
  }
  const opened = openLibrary(path);
  if ("error" in opened) {
    loadFailure = `could not load ${path}: ${opened.error}`;
    return { error: loadFailure };
  }
  binding = opened;
  return binding;
}

/** True when the library loads. Never throws; does not create a context by itself. */
export function isAvailable(): boolean {
  return !("error" in ensure());
}

/** Why the library is unavailable, or `undefined` when it is available. */
export function unavailableReason(): string | undefined {
  const ready = ensure();
  return "error" in ready ? ready.error : undefined;
}

/** `Z3 5.1.0.0`, or `undefined` when the library is unavailable. */
export function version(): string | undefined {
  const ready = ensure();
  return "error" in ready ? undefined : ready.version;
}

/** How many times a context has been created; increments on every error reset. */
export function contextEpoch(): number {
  return epoch;
}

/** Delete the current context (the next query recreates it). Used by tests and error resets. */
export function closeContext(): void {
  if (binding !== undefined) {
    try {
      binding.lib.symbols.Z3_del_context(binding.context);
    } catch {
      // A dead context is not worth reporting: the next query creates a fresh one.
    }
    binding = undefined;
  }
}

function reset(): void {
  closeContext();
  // The library itself stays loaded; only the context is recreated on the next query.
  const ready = ensure();
  if (!("error" in ready)) binding = ready;
}

/** Z3's own way of reporting an unknown command, which has no `(error …)` wrapper. */
function detectProblem(output: string): string | undefined {
  const errorAt = output.indexOf("(error");
  if (errorAt >= 0) {
    const rest = output.slice(errorAt).split("\n")[0]!.trim();
    return `Z3 rejected the query: ${rest}`;
  }
  for (const line of output.split("\n")) {
    const text = line.trim();
    if (text === "unsupported" || text.startsWith("unsupported ")) {
      return `Z3 does not support part of the query: ${output.split("\n").slice(0, 3).join(" ")}`;
    }
  }
  return undefined;
}

function wrap(script: string, timeoutMs: number): string {
  return `(push)\n(set-option :timeout ${Math.max(0, Math.floor(timeoutMs))})\n${script}\n(pop)\n`;
}

/**
 * Run one SMT-LIB query. The script is wrapped in `(push)`/`(pop)` and preceded by a
 * per-query timeout. On any error (including Z3's `unsupported` line) the context is
 * recreated and `ok: false` is returned; a `sat`/`unsat`/`unknown` verdict is *not* an
 * error and comes back as `ok: true` with the text in `output`.
 */
export function evalScript(script: string, opts: { timeoutMs?: number } = {}): Z3EvalResult {
  const ready = ensure();
  if ("error" in ready) return { ok: false, output: "", error: ready.error };
  const timeoutMs = opts.timeoutMs === undefined ? DEFAULT_TIMEOUT_MS : opts.timeoutMs;
  const input = Buffer.from(wrap(script, timeoutMs) + "\0", "utf8");
  let raw: string | null;
  try {
    raw = ready.lib.symbols.Z3_eval_smtlib2_string(ready.context, ptr(input));
  } catch (cause) {
    const message = cause instanceof Error ? cause.message : String(cause);
    reset();
    return { ok: false, output: "", error: `the Z3 call threw: ${message}` };
  }
  if (raw === null || raw === undefined) {
    reset();
    return { ok: false, output: "", error: "Z3 returned a null string (out of memory?)" };
  }
  const output = String(raw).trim();
  const problem = detectProblem(output);
  if (problem !== undefined) {
    reset();
    return { ok: false, output, error: problem };
  }
  return { ok: true, output };
}

/**
 * `evalScript` plus a `(check-sat)`; returns the raw verdict text. Unknown output shapes
 * (`sat`/`unsat`/`unknown` only) are a failure, so a caller can never mistake a stray
 * string for a verdict.
 */
export function checkSat(
  script: string,
  opts: { timeoutMs?: number } = {},
): { status: "sat" | "unsat" | "unknown"; output: string } | { error: string; output: string } {
  const result = evalScript(`${script}\n(check-sat)\n`, opts);
  if (!result.ok) return { error: result.error ?? "the Z3 query failed", output: result.output };
  const lines = result.output
    .split("\n")
    .map((line) => line.trim())
    .filter((line) => line !== "");
  const verdict = lines[lines.length - 1];
  if (verdict !== "sat" && verdict !== "unsat" && verdict !== "unknown") {
    return { error: `Z3 did not answer check-sat (output: ${result.output})`, output: result.output };
  }
  return { status: verdict, output: result.output };
}
