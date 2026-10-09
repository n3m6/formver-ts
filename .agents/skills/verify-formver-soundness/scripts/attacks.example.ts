/**
 * Starter attacks for kernel-attack.ts. Copy this file into $RUN/scratch/, add attacks, and run
 *   bun .agents/skills/verify-formver-soundness/scripts/kernel-attack.ts "$RUN/scratch/attacks.ts"
 * Term builders follow scripts/prove-false.ts; the API is src/kernel/index.ts.
 */
import type * as KernelApi from "../../../../src/kernel/index";
import type { Attack } from "./kernel-attack";

export default function attacks(K: typeof KernelApi): Attack[] {
  const env = K.emptyEnv();
  const int: KernelApi.Mk = () => K.Int;
  const empty: KernelApi.Mk = () => K.Empty;
  const lit = (n: bigint): KernelApi.Mk => K.intLitMk(n);
  const v = (name: string): KernelApi.Mk => K.varMk(name);
  const le = (a: KernelApi.Mk, b: KernelApi.Mk): KernelApi.Mk => K.primMk(K.OP_LE, [a, b]);
  const add = (a: KernelApi.Mk, b: KernelApi.Mk): KernelApi.Mk => K.primMk(K.OP_ADD, [a, b]);
  const sub = (a: KernelApi.Mk, b: KernelApi.Mk): KernelApi.Mk => K.primMk(K.OP_SUB, [a, b]);
  const farkas = (hyps: readonly KernelApi.Mk[], coeffs: readonly bigint[]): KernelApi.Mk => K.farkasMk(hyps, coeffs);

  /** `(x : Int) -> (h1 : lo1) -> (h2 : lo2) -> Empty`, proved by a Farkas combination. */
  const twoHypotheses = (h1: KernelApi.Mk, h2: KernelApi.Mk, coeffs: readonly bigint[]) =>
    K.checkType(
      env,
      K.mk(K.lamMk("x", int, K.lamMk("h1", h1, K.lamMk("h2", h2, farkas([v("h1"), v("h2")], coeffs))))),
      K.mk(K.piMk("x", int, K.piMk("h1", h1, K.piMk("h2", h2, empty)))),
    );

  return [
    {
      name: "x <= 0 and 1 <= x refute each other with multipliers 1, 1",
      expect: "accept",
      run: () => twoHypotheses(le(v("x"), lit(0n)), le(lit(1n), v("x")), [1n, 1n]),
    },
    {
      name: "the same hypotheses with all-zero multipliers (0 <= 0 is no contradiction)",
      expect: "reject",
      run: () => twoHypotheses(le(v("x"), lit(0n)), le(lit(1n), v("x")), [0n, 0n]),
    },
    {
      name: "x <= 0 and 0 <= x are consistent (x = 0), whatever the multipliers",
      expect: "reject",
      run: () => twoHypotheses(le(v("x"), lit(0n)), le(lit(0n), v("x")), [3n, 3n]),
    },
    {
      name: "LeProof 5 3 as evidence of Le 5 3",
      expect: "reject",
      run: () => K.checkType(env, K.LeProof(5n, 3n), K.mk(le(lit(5n), lit(3n)))),
    },
    {
      name: "LeProof 3 5 as evidence of Le 3 5",
      expect: "accept",
      run: () => K.checkType(env, K.LeProof(3n, 5n), K.mk(le(lit(3n), lit(5n)))),
    },
    {
      name: "conversion: x + 1 and 1 + x are the same linear form",
      expect: "accept",
      run: () => K.isConvertible(env, K.mk(K.lamMk("x", int, add(v("x"), lit(1n)))), K.mk(K.lamMk("x", int, add(lit(1n), v("x"))))),
    },
    {
      name: "conversion: x - x is not x",
      expect: "reject",
      run: () => K.isConvertible(env, K.mk(K.lamMk("x", int, sub(v("x"), v("x")))), K.mk(K.lamMk("x", int, v("x")))),
    },
    {
      name: "conversion: Le x y is not Le y x",
      expect: "reject",
      run: () =>
        K.isConvertible(
          env,
          K.mk(K.lamMk("x", int, K.lamMk("y", int, le(v("x"), v("y"))))),
          K.mk(K.lamMk("x", int, K.lamMk("y", int, le(v("y"), v("x"))))),
        ),
    },
  ];
}
