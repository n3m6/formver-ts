# Elaboration notes (milestone 7)

`src/extract/elaborate.ts` turns a `FunctionIR` into a kernel `Term`; `src/verify.ts` runs the
pipeline (lex → parse → cross-check → fragment → SSA → resolution → elaborate → certify → kernel
check) and returns verdicts, diagnostics and an injection plan.  Neither executes user code nor
adds a dependency; every failure is a located diagnostic.

## Elaboration strategy

- **Scope.** The term is a lambda telescope over `signature.binders` (`Binder.type` is already
  "in the context of the preceding binders").  Body slots are resolved with
  `slotTerm`/`deBruijnIndex` against a `Ctx` mirroring the kernel binders, so no index
  arithmetic is hand-written.  Synthetic binders get **negative ids**, which cannot collide with
  the extractor's per-file ids.
- **Statements** are walked in tail position: `local` → `K.letTerm`, `expr` → elaborated for its
  obligations and dropped, `if` → `K.IfLe` (comparison on `Int`) or a `Sum` case split, `switch`
  → the nested `SumCase`, `return` → the packed result.  A ternary in *return position* pushes
  the packing into its branches.  A statement-level expression's **proof-carrying calls are
  bound with a `let` first** (`elabExpr`'s binding pass), so a `@post` or `range` goal mentions a
  *variable*, never a term full of certificates: the SMT encoding cannot read an atom whose
  spine carries `Farkas`/`byContra` terms.  The binding registry is keyed by *call site*
  (`span`), because the extractor copies a call node when it records a fact about its result.
- **Calls** apply the callee binder by binder: parameters, vector lengths, `InRange` proofs
  (literal, binder, fact in scope or an auxiliary obligation), element guards (`elems_a i p`),
  type arguments inferred from the argument types, and the pre-call site's proofs.
- **Locals** whose value carries no proof argument are substituted at every use
  (`TermOptions.inlineSlots`), so a `divFloorSpec` fact about `(lo + hi) / 2` lines up with a
  goal that mentions `let mid = …`.  Division facts are rebuilt from the very terms an
  obligation mentions (`divisionFacts`), skipping proof arguments (their binders make a
  division found there refer to the wrong variables).
- **Postconditions** are certified after a proof-carrying value (index/slice/spread) is bound
  with a `let` and its facts restated about that variable, because `certify` decomposes a goal
  by quoting it and a certificate term inside a quoted `Sigma` hides the proof.

## Loops (`LoopIR`)

`A = loop.stateType` rebuilt from the IR; `B = fun _ : A => Inv s -> Result`;
`m = fun (s : A) => <@decreases>`; and

```text
step = fun (s : A) (px : Le 0 (m s)) (ih : (y : A) -> Le 0 (m y) -> Lt (m y) (m s) -> B y)
           (hinv : Inv s) => if cond then body else rest
loop = fixWf A B m step s0 p0 hinv0 : Result
```

`A`, `B` and `m` are **rebuilt** rather than taken from `LoopIR`'s stored terms: those are
written in the loop's enclosing context and would be read at the wrong depth in a nested loop.
The body context is the final kernel layout `[…, s, px, ih, hinv]`; the extractor's layout is
`[…, s, px, hinv]`, so terms it stored are *renamed* (`fromExtractor`, `binderTypeAt`) instead
of shifted by position.  `continue` becomes `ih s' p↧ p< hinv'`, with `s'` packed by
`packTuple` (the suffix `Sigma` annotation is a beta-redex, so a dependent component type such
as `Vec T n_a` is instantiated by the kernel).  `rest` — the statements after the loop — is the
`else` branch, so the loop term *is* the rest of the function.  `initSites` become `p0`
(`measure-nonneg`) and `hinv0` (`invariant-init`).

## Recursive functions

`A` is the tuple of every non-type-parameter signature binder; `B` absorbs the preconditions:

```text
B     = fun (y : A) => pre_1(y) -> … -> Result(y)
m     = fun (x : A) => <@decreases>                 (mandatory)
step  = fun (x : A) (px : Le 0 (m x)) (ih : …) (pre_1 : …) => body
f     = fun (params…) => fixWf A B m step x0 p0 pre_1 … pre_k
```

Inside the body every parameter (and every proof the signature introduced) stands for the
matching component of `x` (`installProjections`): slots resolve to `fst`/`snd` projections, and
stored terms (`Binder.type`, the result type) are rewritten the same way by `fromExtractor`.
A recursive call is `ih x' p↧ p< pre'`: `x'` is the new argument tuple, and the call site owes
`measure-nonneg`, `measure-decrease` and `pre-call`; `p0` is an auxiliary entry
`measure-nonneg` obligation.  The recursion registry is consulted by `callInfo`, so a
self-call is never `Const(f)` (which does not exist yet).  `fixWf` is opaque: the kernel never
unfolds the definition, so clients use its type only.

## Depth and shifting discipline

- **A site proof is stored with its depth** (`proofs`, `proofAt(id, depth)`): using it deeper
  (the `index` proof a later `elems_a i p` fact applies) weakens it with `shiftTerm`.  The same
  view is handed to `exprTerm` through `TermOptions.proofAt`.
- **A hypothesis carries its depth** (`Hyp`, `hypAt`): it is shifted when used inside a branch,
  never the other way.  Facts made inside a branch do not escape it.
- **A stored term is never trusted to be in the current layout.**  `fromExtractor` maps the
  extractor's binder positions to the elaborator's context (substituting the binders that are
  inlined, lifting the ones that are not); `binderTypeAt` lifts a type this module built past
  the binders pushed after it.  `context` for `certify` is built with `contextTypes`, so the
  kernel self-check runs in exactly the elaborator's layout.
- **A branch binder carries the kernel's own domain** (`Le a b` / `Lt b a`), not the
  extractor's rendering of the source condition (`Eq`, `Not (Eq …)`): a hypothesis whose proof
  does not have the proposition it is stated with makes `certify` reconstruct an equality row it
  cannot prove.

## Verdicts and kernel admission

Any `failed` site ⇒ `failed`; else any `smt-only` ⇒ `smt-only`; else
`K.checkType(env, term, signature.type)` must accept the whole term, and only then is the
function added as a **`def`** (same-file calls resolve, `axiomsUsed` stays `[]`).  A
non-certified function is admitted as an **`external`** (lenient mode), each caller marked in
`dependsOnUncertified`.  A kernel rejection of a complete term becomes an `internal` diagnostic
with `K.formatKernelError`; an exception inside the elaborator becomes a located `internal`
diagnostic, never a crash.

## The `verify()` result (for milestone 8)

`verify(path, source, opts?: { strict?, timeoutMs?, env?, readFile?, resolver?, verifyImports? })`

- `path`, `strict`, `ok`, `diagnostics[]`, `axioms[]` (`[]`), `env`, `plan[]`, `externals[]`.
- `functions[]`: `{ name, exported, span, status: "certified"|"smt-only"|"failed"|"rejected",
  certified, obligations[], dependsOnUncertified[] }` with `obligations[] = { siteId, kind,
  span, text, status, reason?, path?, counterexample? }`.
- Milestone 8 must know: loops and recursion are `def`s whose body is a `fixWf` application, so
  the injection plan is the only runtime evidence — keep the loop-head invariant/measure checks
  and the recursive call's checks; `certify`'s own self-check now runs in the elaborator's
  layout, and `buildContext` (`src/vc/certify.ts`) no longer mutates the environment array it
  builds (a `Pi`/`Sigma` value captured it and read a later variable).

## Known limits of this part

- A **loop-carried vector** is rejected: `LoopIR` carries no length for it, so `A` cannot be
  rebuilt (`valueType` throws a located failure).
- A function with several `@post` tags: the nth-post path is computed by
  `conjunctionProjection(i, count)` from the right-nested `And`; a single post needs no
  projection.
- The certificate search in `certify` is the slow part of verifying `binarySearch` (seconds per
  loop obligation): the division specification and the vector bounds give it large integer
  coefficients.  `bun test`'s e2e files raise the default timeout accordingly.
