/**
 * Shared term fixtures for the kernel tests.
 *
 * Every term is built with the exported de Bruijn-safe builder (`mk`/`piMk`/`lamMk`/...),
 * so the tests exercise the same public surface the untrusted elaborator will use.
 */
import { expect } from "bun:test";
import * as K from "../../src/kernel/index";

/** Unwraps a successful result, failing the test with the kernel's diagnostic. */
export function expectOk<T>(result: K.Result<T>): T {
  if (!result.ok) throw new Error(`expected success, got: ${K.formatKernelError(result.error)}`);
  return result.value;
}

/** Unwraps a failed result, failing the test when the kernel accepted. */
export function expectErr<T>(result: K.Result<T>): K.KernelError {
  if (result.ok) throw new Error("expected the kernel to reject, but it accepted");
  return result.error;
}

export const expectReason = <T>(result: K.Result<T>, reason: K.KernelErrorReason): void => {
  expect(expectErr(result).reason).toBe(reason);
};

// ---------------------------------------------------------------------------
// Core combinators
// ---------------------------------------------------------------------------

/** `(A : Type 0) -> A -> A` */
export const idType: K.Term = K.mk(
  K.piMk("A", K.sortMk(0), K.piMk("x", K.varMk("A"), K.varMk("A"))),
);

/** `fun A x => x` */
export const identity: K.Term = K.mk(
  K.lamMk("A", K.sortMk(0), K.lamMk("x", K.varMk("A"), K.varMk("x"))),
);

export const idAt = (a: K.Term): K.Term => K.app(identity, a);

/** `(A : Type 0) -> (B : Type 0) -> A -> B -> A` */
export const constType: K.Term = K.mk(
  K.piMk(
    "A",
    K.sortMk(0),
    K.piMk("B", K.sortMk(0), K.piMk("x", K.varMk("A"), K.piMk("y", K.varMk("B"), K.varMk("A")))),
  ),
);

/** `fun A B x y => x` */
export const constFn: K.Term = K.mk(
  K.lamMk(
    "A",
    K.sortMk(0),
    K.lamMk("B", K.sortMk(0), K.lamMk("x", K.varMk("A"), K.lamMk("y", K.varMk("B"), K.varMk("x")))),
  ),
);

/** `(A B C : Type 0) -> (B -> C) -> (A -> B) -> A -> C` */
export const composeType: K.Term = K.mk(
  K.piMk(
    "A",
    K.sortMk(0),
    K.piMk(
      "B",
      K.sortMk(0),
      K.piMk(
        "C",
        K.sortMk(0),
        K.piMk(
          "f",
          K.piMk("_", K.varMk("B"), K.varMk("C")),
          K.piMk(
            "g",
            K.piMk("_", K.varMk("A"), K.varMk("B")),
            K.piMk("x", K.varMk("A"), K.varMk("C")),
          ),
        ),
      ),
    ),
  ),
);

/** `fun A B C f g x => f (g x)` */
export const compose: K.Term = K.mk(
  K.lamMk(
    "A",
    K.sortMk(0),
    K.lamMk(
      "B",
      K.sortMk(0),
      K.lamMk(
        "C",
        K.sortMk(0),
        K.lamMk(
          "f",
          K.piMk("_", K.varMk("B"), K.varMk("C")),
          K.lamMk(
            "g",
            K.piMk("_", K.varMk("A"), K.varMk("B")),
            K.lamMk("x", K.varMk("A"), K.appMk(K.varMk("f"), K.appMk(K.varMk("g"), K.varMk("x")))),
          ),
        ),
      ),
    ),
  ),
);

// ---------------------------------------------------------------------------
// Church numerals
// ---------------------------------------------------------------------------

/** `Nat = (A : Type 0) -> (A -> A) -> A -> A` */
export const natType: K.Term = K.mk(
  K.piMk(
    "A",
    K.sortMk(0),
    K.piMk(
      "f",
      K.piMk("_", K.varMk("A"), K.varMk("A")),
      K.piMk("x", K.varMk("A"), K.varMk("A")),
    ),
  ),
);

const natMk: K.Mk = () => natType;
const endoMk = (): K.Mk => K.piMk("_", K.varMk("A"), K.varMk("A"));

function applyNTimes(fn: K.Mk, n: number, x: K.Mk): K.Mk {
  let out = x;
  for (let i = 0; i < n; i += 1) out = K.appMk(fn, out);
  return out;
}

/** The Church numeral `n`: `fun A f x => f (f ... (f x))`. */
export function church(n: number): K.Term {
  return K.mk(
    K.lamMk(
      "A",
      K.sortMk(0),
      K.lamMk("f", endoMk(), K.lamMk("x", K.varMk("A"), applyNTimes(K.varMk("f"), n, K.varMk("x")))),
    ),
  );
}

/** `fun n A f x => f (n A f x)`. */
export const suc: K.Term = K.mk(
  K.lamMk(
    "n",
    natMk,
    K.lamMk(
      "A",
      K.sortMk(0),
      K.lamMk(
        "f",
        endoMk(),
        K.lamMk(
          "x",
          K.varMk("A"),
          K.appMk(K.varMk("f"), K.appMk(K.appMk(K.appMk(K.varMk("n"), K.varMk("A")), K.varMk("f")), K.varMk("x"))),
        ),
      ),
    ),
  ),
);

/** `Nat -> Nat` */
export const sucType: K.Term = K.pi("n", natType, natType);

/** `fun m n A f x => m A f (n A f x)`. */
export const plus: K.Term = K.mk(
  K.lamMk(
    "m",
    natMk,
    K.lamMk(
      "n",
      natMk,
      K.lamMk(
        "A",
        K.sortMk(0),
        K.lamMk(
          "f",
          endoMk(),
          K.lamMk(
            "x",
            K.varMk("A"),
            K.appMk(
              K.appMk(K.appMk(K.varMk("m"), K.varMk("A")), K.varMk("f")),
              K.appMk(K.appMk(K.appMk(K.varMk("n"), K.varMk("A")), K.varMk("f")), K.varMk("x")),
            ),
          ),
        ),
      ),
    ),
  ),
);

/** `Nat -> Nat -> Nat` */
export const plusType: K.Term = K.pi("m", natType, K.pi("n", natType, natType));

// ---------------------------------------------------------------------------
// Dependent pairs
// ---------------------------------------------------------------------------

/** `Sigma (A : Type 0). A -> A` — a genuinely dependent pair type. */
export const depSigma: K.Term = K.sigma("A", K.sort(0), K.pi("_", K.varTerm(0), K.varTerm(1)));

/** `fun x => x`, the second component of a `depSigma` pair. */
export const endoId: K.Term = K.lam("x", K.Unit, K.varTerm(0));

/** `<Unit, fun x => x> : Sigma (A : Type 0). A -> A` */
export const depPair: K.Term = K.pair(depSigma, K.Unit, endoId);

// ---------------------------------------------------------------------------
// Transport (`J`)
// ---------------------------------------------------------------------------

const A = (): K.Mk => K.varMk("A");
const P = (): K.Mk => K.varMk("P");
const aVar = (): K.Mk => K.varMk("a");
const bVar = (): K.Mk => K.varMk("b");
const pVar = (): K.Mk => K.varMk("p");
const paVar = (): K.Mk => K.varMk("pa");
const eqOf = (x: K.Mk, y: K.Mk): K.Mk => K.primMk(K.OP_EQ, [A(), x, y]);

/**
 * `transport : (A : Type 0) -> (P : A -> Type 0) -> (a b : A) -> Eq A a b -> P a -> P b`
 * implemented as `fun A P a b p pa => J A a (fun b' _ => P b') pa b p`.
 */
export const transport: K.Term = K.mk(
  K.lamMk(
    "A",
    K.sortMk(0),
    K.lamMk(
      "P",
      K.piMk("_", A(), K.sortMk(0)),
      K.lamMk(
        "a",
        A(),
        K.lamMk(
          "b",
          A(),
          K.lamMk(
            "p",
            eqOf(aVar(), bVar()),
            K.lamMk(
              "pa",
              K.appMk(P(), aVar()),
              K.primMk(
                K.OP_J,
                [
                  A(),
                  aVar(),
                  K.lamMk("b2", A(), K.lamMk("p2", eqOf(aVar(), K.varMk("b2")), K.appMk(P(), K.varMk("b2")))),
                  paVar(),
                  bVar(),
                  pVar(),
                ],
                0,
              ),
            ),
          ),
        ),
      ),
    ),
  ),
);

export const transportType: K.Term = K.mk(
  K.piMk(
    "A",
    K.sortMk(0),
    K.piMk(
      "P",
      K.piMk("_", A(), K.sortMk(0)),
      K.piMk(
        "a",
        A(),
        K.piMk(
          "b",
          A(),
          K.piMk("p", eqOf(aVar(), bVar()), K.piMk("pa", K.appMk(P(), aVar()), K.appMk(P(), bVar()))),
        ),
      ),
    ),
  ),
);
