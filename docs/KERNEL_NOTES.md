# Kernel notes (milestone 2)

Trusted core in `src/kernel/`: it imports only from inside that directory (no Bun APIs, no
npm packages, no `console`). The public surface is `src/kernel/index.ts`.

## Terms (`term.ts`)

- `Term` is exactly specification 6.1.1. Binding is by de Bruijn **index**; `name` prints only.
- `Scope` + `Mk` (`mk`, `piMk`, `lamMk`, `sigmaMk`, `letMk`, `varMk`, `appMk`, `primMk`, ...)
  build terms without index arithmetic; `mk(f)` runs a builder in the empty scope.
- `erase(term)`: `Sort`/`Pi`/`Sigma`/`Farkas` become `{tag:"Erased"}`; `Lam` domains, `Pair`
  Sigma annotations, `Let` types and `Prim` levels are dropped. `Lam`/`Let` keep their binder,
  so every surviving index keeps its meaning; erased positions are never inspected.

## Values, eval, quote (`value.ts`, `eval.ts`, `quote.ts`)

- `Value = Sort | Pi | Lam | Sigma | Pair | IntLit | Farkas | Neutral`.
- Value environments are indexed by de Bruijn **level**: `env[i]` is the value of level `i`,
  so `Var n` reads `env[len-1-n]`. Fresh variables are created at level `env.length`, which
  makes levels globally fresh; `quote(env, depth, v)` maps level `l` to `Var (depth-1-l)`.
- `Closure = { name, body, env }`; applying one needs the global `Env`, so `applyClosure`
  lives in `eval.ts`. Evaluation is eager: beta, delta (definitions unless `opaque`), zeta.
- A primitive whose `reduce` returns `undefined`, or that is not yet saturated, becomes a
  neutral whose head is `Prim { op, level, args }` plus a spine, so `fixWf ... x` is a value.

## The registry (`builtins.ts`)

- `PRIMS: Record<PrimOp, PrimInfo>` (frozen; untrusted code cannot swap a rule), plus
  `lookupPrim(op)`. `PrimInfo = { name, arity, typeFor(level), reduce?(args, ctx),
  irrelevant?[], convArgs?(a, b) }`.
  - `typeFor(level)` is a closed Pi telescope; `check.ts` walks it, checking each argument
    against the domain and substituting into the codomain.
  - `reduce(args, ctx)` returns `Value | undefined`; `undefined` means stuck. `ctx` offers
    `apply`, `evalIn` and `lookup`.
  - `irrelevant` lists 0-based positions that `convValue` skips (proof irrelevance) and that
    atom keys must erase. `convArgs(a, b)` returns a verdict or `undefined`, in which case
    the default position-wise comparison applies.
- Milestone 2 registers `Empty, Unit, tt, Sum, inl, inr, case, absurd, Eq, refl, J`, plus
  `Int` and `Le` as **type-only placeholders** so `IntLit` and `Farkas` are usable now.
  `And`/`Not` are *definitions* (over `Sigma` and `Pi`) inserted through `addDecl` by
  `emptyEnv()`; the prelude contains zero axioms.

## What milestone 3 must do

- Add ops by adding `PRIMS` entries only — `eval`, `check` and `conv` need no structural
  change: `Int` (`add`, `sub`, `neg`, `mulConst`), `Le` (add `convArgs`), `ifLe`, `byContra`,
  `intEq`, `Vec`, `len`, `vecBounds`, `get`, `append`, `slice`, `castVec`, `fixWf` (omit
  `reduce`: that is what keeps it opaque), `divFloor`, `divTrunc`.
- For `Int` values, add a `Linear` variant to `Value` (constant plus atom→bigint map) with
  `IntLit` as the atom-free case, handled in `quote`, `convValue` and the `reduce` rules;
  conversion of `Int` compares linear forms; `Le`'s `convArgs` compares the linear forms of
  `b - a` and `d - c`. Atom key: canonical text of the atom's quoted normal form with
  `irrelevant` positions replaced by a placeholder.
- `Lt`/`InRange` are definitions: append them to `builtinDecls()` (they enter through
  `addDecl`, never as axioms). In `farkas.ts`, replace the literal-only branch of `rowOfLe`
  with rows from the linear form of `t - s`; `tightenRow` and `checkCertificate` are final,
  and `src/vc/linear.ts` must match their arithmetic exactly.
- Invariants to preserve: no `Type l : Type l`; `fixWf` never unfolds; `conv.ts`'s eta rules
  assume the two values have convertible types, so never call `convValue` on ill-typed ones.
