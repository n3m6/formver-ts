/**
 * The kernel's prove-`false` cases, for step 7 of `bun run demo` (specification section 9.1).
 *
 * Every case here is an attempt to make the trusted kernel in `src/kernel/` accept a proof of
 * `false`, or to make its conversion identify two things that are not the same.  Each one must
 * be rejected, with the reason recorded in `expected`; `test/kernel/soundness3.test.ts` asserts
 * the same scenarios with `bun:test`, and `test/kernel/proveFalse.test.ts` re-runs this list so
 * the demo cannot drift from the kernel.  The cases are re-stated here (rather than imported
 * from the test) so that the demo prints the kernel's own rejection reasons without loading a
 * test runner: the terms are built with the public API only, exactly like the untrusted
 * elaborator builds them.
 *
 * A case either produces a `K.Result` (which must be an error) or a conversion answer (which
 * must be `false`); `runProveFalseCase` turns either into the string the demo prints.
 */
import * as K from "../src/kernel/index";

/** What the kernel must answer: an error reason, or a refusal to convert. */
export type Rejection = K.KernelErrorReason | "not-convertible";

export interface ProveFalseCase {
  /** What the attempt tries to prove. */
  readonly name: string;
  /** The reason the kernel must give. */
  readonly expected: Rejection;
  /** Run the attempt: a `Result` to reject, or a conversion to refuse. */
  readonly run: () => K.Result<unknown> | boolean;
}

// ---------------------------------------------------------------------------
// Term builders (the same shapes test/kernel/helpers3.ts uses)
// ---------------------------------------------------------------------------

const env = K.emptyEnv();

const int: K.Mk = () => K.Int;
const empty: K.Mk = () => K.Empty;
const lit = (n: bigint): K.Mk => K.intLitMk(n);
const v = (name: string): K.Mk => K.varMk(name);

const le = (a: K.Mk, b: K.Mk): K.Mk => K.primMk(K.OP_LE, [a, b]);
const lt = (a: K.Mk, b: K.Mk): K.Mk => K.appManyMk(K.constMk(K.LT_NAME), [a, b]);
const add = (a: K.Mk, b: K.Mk): K.Mk => K.primMk(K.OP_ADD, [a, b]);
const sub = (a: K.Mk, b: K.Mk): K.Mk => K.primMk(K.OP_SUB, [a, b]);
const vec = (a: K.Mk, n: K.Mk): K.Mk => K.primMk(K.OP_VEC, [a, n]);
const and = (a: K.Mk, b: K.Mk): K.Mk => K.appManyMk(K.constMk(K.AND_NAME), [a, b]);
const byContra = (a: K.Mk, b: K.Mk, k: K.Mk): K.Mk => K.primMk(K.OP_BY_CONTRA, [a, b, k]);
const farkas = (hyps: readonly K.Mk[], coeffs: readonly bigint[]): K.Mk => K.farkasMk(hyps, coeffs);
const leProof = (a: bigint, b: bigint): K.Mk => () => K.LeProof(a, b);

/** `get A n v i p` with the argument list the case wants (one short = an arity error). */
const get = (a: K.Mk, n: K.Mk, v0: K.Mk, i: K.Mk, p?: K.Mk): K.Mk =>
  K.primMk(K.OP_GET, p === undefined ? [a, n, v0, i] : [a, n, v0, i, p]);

// ---------------------------------------------------------------------------
// The `fixWf` cases
//
// `fixWf {0} Int (fun _ => Int) (fun z => z) step 5 (LeProof 0 5)`, with the real induction
// hypothesis `(y : Int) -> Le 0 y -> Lt y x -> Int` for the measure `z => z`.
// ---------------------------------------------------------------------------

const fixAt = (step: K.Mk): K.Term =>
  K.mk(
    K.primMk(
      K.OP_FIX_WF,
      [int, K.lamMk("_", int, int), K.lamMk("z", int, v("z")), step, lit(5n), leProof(0n, 5n)],
      0,
    ),
  );

const goodIh = (): K.Mk =>
  K.piMk("y", int, K.piMk("py", le(lit(0n), v("y")), K.piMk("d", lt(v("y"), v("x")), int)));

// ---------------------------------------------------------------------------
// The cases
// ---------------------------------------------------------------------------

export const proveFalseCases: readonly ProveFalseCase[] = [
  {
    name: "Farkas certificate whose multipliers bound is not negative",
    expected: "farkas-invalid",
    run: () =>
      K.checkType(
        env,
        K.mk(
          K.lamMk(
            "x",
            int,
            K.lamMk(
              "h1",
              le(v("x"), lit(0n)),
              K.lamMk("h2", le(lit(0n), v("x")), farkas([v("h1"), v("h2")], [1n, 1n])),
            ),
          ),
        ),
        K.mk(
          K.piMk(
            "x",
            int,
            K.piMk("h1", le(v("x"), lit(0n)), K.piMk("h2", le(lit(0n), v("x")), empty)),
          ),
        ),
      ),
  },
  {
    name: "Farkas certificate with a negative multiplier",
    expected: "farkas-negative-coefficient",
    run: () =>
      K.checkType(
        env,
        K.mk(K.lamMk("h", le(lit(2n), lit(1n)), farkas([v("h")], [-1n]))),
        K.mk(K.piMk("h", le(lit(2n), lit(1n)), empty)),
      ),
  },
  {
    name: "Farkas certificate over a hypothesis that is not `Le`",
    expected: "farkas-not-a-le-hypothesis",
    run: () =>
      K.checkType(
        env,
        K.mk(K.lamMk("h", K.primMk(K.OP_EQ, [int, lit(0n), lit(0n)]), farkas([v("h")], [1n]))),
        K.mk(K.piMk("h", K.primMk(K.OP_EQ, [int, lit(0n), lit(0n)]), empty)),
      ),
  },
  {
    name: "`get` without a bounds proof",
    expected: "prim-arity",
    run: () => K.inferType(env, K.mk(K.lamMk("w", vec(int, lit(3n)), get(int, lit(3n), v("w"), lit(1n))))),
  },
  {
    name: "`get` with a bounds proof for a different vector and index",
    expected: "type-mismatch",
    run: () =>
      K.inferType(
        env,
        K.mk(
          K.lamMk(
            "w",
            vec(int, lit(3n)),
            K.lamMk(
              "p",
              and(le(lit(0n), lit(5n)), lt(lit(5n), lit(7n))),
              get(int, lit(3n), v("w"), lit(5n), v("p")),
            ),
          ),
        ),
      ),
  },
  {
    name: "`append` without its length proof",
    expected: "prim-arity",
    run: () =>
      K.inferType(
        env,
        K.mk(
          K.lamMk(
            "u",
            vec(int, lit(2n)),
            K.lamMk("w", vec(int, lit(3n)), K.primMk(K.OP_APPEND, [int, lit(2n), lit(3n), v("u"), v("w")])),
          ),
        ),
      ),
  },
  {
    name: "`fixWf`: the induction hypothesis called without a decrease proof",
    expected: "type-mismatch",
    run: () =>
      K.inferType(
        env,
        fixAt(
          K.lamMk(
            "x",
            int,
            K.lamMk(
              "px",
              le(lit(0n), v("x")),
              K.lamMk("ih", goodIh(), K.appManyMk(v("ih"), [sub(v("x"), lit(1n)), v("px")])),
            ),
          ),
        ),
      ),
  },
  {
    name: "`fixWf`: `Le (m y) (m x)` given where `Lt (m y) (m x)` is required",
    expected: "type-mismatch",
    run: () =>
      K.inferType(
        env,
        fixAt(
          K.lamMk(
            "x",
            int,
            K.lamMk(
              "px",
              le(lit(0n), v("x")),
              K.lamMk(
                "ih",
                goodIh(),
                K.appManyMk(v("ih"), [
                  sub(v("x"), lit(1n)),
                  v("px"),
                  byContra(sub(v("x"), lit(1n)), v("x"), K.lamMk("k", lt(v("x"), sub(v("x"), lit(1n))), farkas([v("k")], [1n]))),
                ]),
              ),
            ),
          ),
        ),
      ),
  },
  {
    name: "`Type 0 : Type 0`",
    expected: "type-mismatch",
    run: () => K.checkType(env, K.sort(0), K.sort(0)),
  },
  {
    name: "`ifLe` with the two branch hypothesis types swapped",
    expected: "type-mismatch",
    run: () =>
      K.inferType(
        env,
        K.IfLe(
          0,
          K.Int,
          K.intLit(1n),
          K.intLit(2n),
          // `yes` must take `Le 1 2` and `no` must take `Lt 2 1`.
          K.lam("_", K.Lt(K.intLit(2n), K.intLit(1n)), K.intLit(10n)),
          K.lam("_", K.Le(K.intLit(1n), K.intLit(2n)), K.intLit(20n)),
        ),
      ),
  },
  {
    name: "`byContra` with a hypothesis of the wrong direction",
    expected: "type-mismatch",
    run: () =>
      K.inferType(
        env,
        K.mk(K.lamMk("k", lt(lit(0n), lit(1n)), byContra(lit(0n), lit(1n), v("k")))),
      ),
  },
  {
    name: "conversion: `Vec A n` must not be `Vec A (n + 1)`",
    expected: "not-convertible",
    run: () =>
      K.isConvertible(
        env,
        K.mk(K.lamMk("n", int, vec(int, v("n")))),
        K.mk(K.lamMk("n", int, vec(int, add(v("n"), lit(1n))))),
      ),
  },
  {
    name: "conversion: a `fixWf` application must not unfold to its step's result",
    expected: "not-convertible",
    run: () =>
      K.isConvertible(
        env,
        fixAt(
          K.lamMk(
            "x",
            int,
            K.lamMk(
              "px",
              le(lit(0n), v("x")),
              K.lamMk(
                "ih",
                K.piMk("y", int, K.piMk("py", le(lit(0n), v("y")), K.piMk("d", lt(v("y"), v("x")), int))),
                lit(42n),
              ),
            ),
          ),
        ),
        K.intLit(42n),
      ),
  },
];

export interface RejectionOutcome {
  /** The error reason, `not-convertible`, or `ACCEPTED` when the attempt wrongly succeeded. */
  readonly rejection: string;
  /** The kernel's own message, when it rejected with an error. */
  readonly message?: string;
}

/** Run one case and report how the kernel answered. */
export function runProveFalseCase(entry: ProveFalseCase): RejectionOutcome {
  const outcome = entry.run();
  if (typeof outcome === "boolean") {
    return { rejection: outcome ? "ACCEPTED" : "not-convertible" };
  }
  if (outcome.ok) return { rejection: "ACCEPTED" };
  return { rejection: outcome.error.reason, message: outcome.error.message };
}
