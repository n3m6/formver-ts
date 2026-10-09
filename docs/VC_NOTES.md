# Obligation and Z3 notes (milestone 6)

Untrusted layer at `src/vc/`: `z3.ts` (the `bun:ffi` binding), `linear.ts` (linear
normalization, GCD tightening, case splitting), `smtlib.ts` (SMT-LIB printing, model
decoding), `obligations.ts` (the record) and `certify.ts` (validity, counterexamples,
certificates, proof terms). Nothing imports `typescript`, executes user code, or has runtime
dependencies; the kernel is still the only trusted part.

## The obligation record (`obligations.ts`)

```ts
export interface Obligation {
  id: string; kind: DiagnosticKind; span: Span;
  hypotheses: K.Term[];              // propositions, IN ORDER, in the ambient context
  goal: K.Term;                      // proposition, same context
  atomNames?: Record<string, string>; // K.keyOfValue key -> user-facing name
  proofs?: K.Term[];                 // one proof term per hypothesis, same order
  context?: K.Term[];                // ambient binder types, outermost first
}
```
- `hypotheses` and `goal` are kernel terms in the context the elaborator is already inside;
  **order matters**, since the Farkas multipliers index `hypotheses` exactly, as does the proof.
- `proofs[i]` is the proof *term* of `hypotheses[i]` — the only way to name a derived proof
  such as `elems_a i p`. With `context` but no `proofs`, `certify` looks the proposition up
  among the binder types, and **rejects** the obligation when it is absent. Without
  `context` the fallback is "the hypotheses are the innermost binders" (`Var (n-1-i)`).
- `context[p]` is the binder at position `p`, typed in the context of the *preceding*
  binders (what `src/extract`'s `Binder.type` already is). `certify` builds the kernel `Ctx`
  from it, which makes atom keys exact and enables the self-check.
- `atomNames` maps `K.keyOfValue` strings to names. A binder bound at level `l` (assigned in
  binding order, so the outermost of `d` binders is level 0) has key `Var(l)`;
  `contextAtomNames(depth, names)` builds the whole map.

## The certify contract

```ts
export type CertifyStatus = "certified" | "smt-only" | "failed";
export interface CertifyResult { status; proof?; proofType?; multipliers?;
                                 counterexample?; path?; reason?; }
export function certify(env: K.Env, ob: Obligation, opts?: { timeoutMs?: number }): CertifyResult;
```
- `certified`: a proof was found. `proof` proves `proofType` (`ob.goal`), and — whenever
  `context` was supplied — the kernel accepted it before it was returned. A `Le` goal
  becomes `byContra a b (k => Farkas [hyps…, k] [λ…])`; conjunctions are pairs, `===` is
  `intEq a b p q`, `||` is `inl`/`inr`/an `ifLe` split, `!==` and `||` hypotheses are
  `ifLe`/`case` eliminations, and a contradictory context gives `absurd goal (Farkas …)`.
- `smt-only`: Z3 proved the obligation (hypotheses + negated goal is `unsat`) but no
  certificate exists for the tightened rows — an integer fact needing cutting planes. No
  `proof`; strict mode must fail it.
- `failed`: invalid (`counterexample` filled in, `path` locating the case) or not proven
  (`unknown`, a Z3 error, Z3 unavailable, an unencodable hypothesis, a missing proof).
- `multipliers`: the `λ` of the first certificate found; `path` is the case split (`ifLe`,
  `case`) that produced the result (the caller has better source text for diagnostics).
- It never throws: an internal error becomes `failed` with a `reason`.

## Rows, and agreement with the kernel

`linear.ts` deliberately duplicates `src/kernel/farkas.ts`: `tightenRow`, `checkCertificate`,
row extraction (`Le s t` gives the row of the linear form of `s - t`, bound `-k`) and the
form arithmetic. It shares only `K.keyOfValue` (atom identity) and `K.formOf` (what is
linear), so a bug here is a rejected certificate, never a weakened kernel.
`test/vc/linear.test.ts` compares rows (keys, coefficients, bounds), tightening and
`checkCertificate` against the kernel's on a corpus including `2x <= 1`, `2x <= 2`, negative
constants, zero coefficients, `Lt`, opaque `get` atoms and `__proto__` keys. Evaluation uses
`values[level] = Var level`, so the atoms the kernel later cancels have exactly these keys.

## The timeout mechanism (verified on Z3 5.1.0.0)

`(set-option :timeout N)` works through `Z3_eval_smtlib2_string` and yields `unknown`
instead of hanging: a 13-pigeon/12-hole pigeonhole instance takes ~10 s alone, with
`:timeout 200` answered `unknown` after 203 ms and with `:timeout 1000` after 1003 ms. Two
measured cautions: the option is **not** scoped by `push`/`pop`, so every query sets it
explicitly, and `:timeout 0` means "no timeout", not "immediately" (9.7 s, same instance).
The binding prefixes every query with `(push)`, `(set-option :timeout N)`, the script,
`(pop)`, and defaults to `z3.DEFAULT_TIMEOUT_MS` (10 s).

## Errors and context resets

Z3 reports errors inline (`(error "…")`) and keeps going; an unknown *command* returns a
bare `unsupported` line. `evalScript` treats either as a failure, never a verdict: it
returns `{ ok: false, output, error }`, and because the state may be unbalanced afterwards
(an unclosed `(push)`) the context is deleted and recreated (`contextEpoch()` increments) —
the test asserts the failure *and* that the next query still answers. `sat`/`unsat`/
`unknown` come back with `ok: true` and `unknown` is never turned into a verdict.
`(get-model)`/`(get-value)` need a `(check-sat)` in the same script ("model is not
available" otherwise), so the certificate search asks `(check-sat)` first.

The library is loaded lazily: importing `z3.ts` never throws when `.z3/libz3.so` is missing
(`DEP_VERIFY_LIBZ3` overrides the path, resolved against the repo). `isAvailable()` and
`unavailableReason()` report it, `version()` returns `Z3 5.1.0.0`, `certify` degrades to
`failed`, and `test/vc` skips with a message.

## What milestone 7 must know

- Build one `Obligation` per `ObligationSite`: `kind`/`span` from the site, `goal` from
  `goalTerm(site, { result })`, `hypotheses` from `exprTerm(ctx, fact.prop)`, `proofs` from
  `slotTerm`/`deBruijnIndex` per fact, `context` from `site.context[i].type`, `atomNames`
  from `contextAtomNames`.
- Insert `result.proof` where the hole is, unshifted: it is a term in the site's context and
  `result.proofType` is `ob.goal`. Never fill a `smt-only`/`failed` obligation as if it were
  proven (lenient mode injects a runtime check instead).
- `certified` is only as trustworthy as the obligation: pass `context` so `certify` runs the
  kernel self-check; otherwise the kernel check of the elaborated term is the trust
  boundary. A malformed obligation (an ill-typed goal) is rejected by the self-check.
- Divisions by a constant are opaque atoms: `divFloor`/`divTrunc` are never printed as
  `div`/`mod` (SMT-LIB rounds differently), so `a[i]`-style facts must come from the
  hypotheses (`divFloorSpec`, element guards), not from arithmetic inside the goal.
- Counterexamples are keyed by `atomNames`; Z3 picks arbitrary values, so evaluate them
  against the spec, never compare them to constants.
