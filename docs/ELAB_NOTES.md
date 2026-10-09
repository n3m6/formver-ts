# Elaboration notes (milestone 7, part A)

`src/extract/elaborate.ts` turns a `FunctionIR` into a kernel `Term`; `src/verify.ts` runs the
pipeline (lex → parse → cross-check → fragment → SSA → resolution → elaborate → certify → kernel
check) and returns verdicts, diagnostics and an injection plan.  Neither executes user code nor adds
a dependency; every failure is a located diagnostic.

## Elaboration strategy

- **Scope.** The term is a lambda telescope over `signature.binders` (a `Binder.type` is already
  "in the context of the preceding binders", i.e. a `Lam` domain); body slots are resolved with
  `slotTerm`/`deBruijnIndex` against a `Ctx` mirroring the kernel binders, so no index arithmetic is
  hand-written.  Synthetic binders get **negative ids**, which cannot collide with the extractor's
  per-file ids (`deBruijnIndex`/`sameSlot` match by id).
- **Statements** are walked in tail position: `local` → `K.letTerm`, `expr` → elaborated for its
  obligations and dropped, `if` → `K.IfLe` (comparison on `Int`) or a `Sum` case split (union
  discriminant) with the branch hypothesis or payload in scope, `switch` → the nested `SumCase` the
  union encoding needs, `return` → the packed result.  A ternary in *return position* pushes the
  packing into its branches (`ifLe … (h => ⟨a, post-a⟩) (h' => ⟨b, post-b⟩)`), which gives `abs`
  its per-branch `@post`; a conditional nested deeper in a returned value is not split.
- **Expressions** come from `fragment.ts`'s `exprTerm`, extended with one hook
  (`TermOptions.override`) for `call` (the callee's whole telescope) and `append` (one bound proof
  per spread part), which need more than the IR supplies.  Arithmetic, comparisons, `&&`/`||`/`!`,
  ternaries, `index` (`K.Get` with the site's proof), `slice`, `append`, object literals and the
  prelude's `Math.*` are shared with milestone 5, so the layers cannot drift.
- **Calls** apply the callee binder by binder: parameters from the arguments, vector lengths from
  `vecLength`, `InRange` proofs (a literal by computation, a parameter by its proof binder, else a
  fact in scope or an auxiliary obligation), element guards (`elems_a i p`; only a caller that
  received the same `readonly number[]` parameter can supply one, justified by the runtime guard),
  type arguments inferred from the argument types, and the pre-call site's precondition proofs.
- **Returns** are packed per `ResultLayout`: `⟨r, ⟨InRange r, posts⟩⟩` for `Int`,
  `⟨m, ⟨Vec T m, posts⟩⟩` for arrays, the bare value for a union or generic result.  A `@post` is
  certified *after* a proof-carrying value (call, index, slice, spread) is bound with a `let` and
  its derived facts restated about that variable: `certify` decomposes a goal by quoting it, and a
  certificate term inside a quoted `Sigma` is renumbered wrongly, hiding the proof.  Plain values
  (`-x`, `s.a`) stay inline so linear reasoning over the parameters still applies.
- **Narrowing.** A `switch`/`if` on a discriminant case-splits the union; each branch binds the
  variant's payload record and gains its `InRange` field facts.  A *conditional precondition*
  (`@pre s.kind === "square" ? A : B`) is eliminated with the split: the motive is
  `preAt(s') -> … -> Result`, the split is applied to the precondition's proof and each branch
  receives its own instance — what makes `shape` certify.

## Holes: ordering and filling

- Each `ObligationSite` becomes one `Obligation`: `kind`/`span`/`text` from the site, `goal` from
  `exprTerm(ctx, site.goal, { result, proofs })`, `hypotheses`/`proofs` from the elaborator's facts
  plus the site's own, `context` from the current binder types (so `certify` re-checks the proof)
  and `atomNames` from `contextAtomNames`.
- **Facts** carry a proposition *and* its proof, tagged with the depth they were built at; they are
  shifted only when used deeper, and facts made inside a branch never escape it.  Origins include
  parameters and vector bounds, preconditions, conditions, case-split hypotheses, the expression
  facts of a node and the division lemmas.  An `Eq` hypothesis is transported (by `J`) into the two
  `Le` facts it implies, because `certify`'s construction for one is rejected by the kernel.
- **Order.** Sites are certified in source order as the walk reaches them — a node's children first,
  then its own sites (so `a[i] + 1` uses the `index` proof in its `range` goal), then the
  statement's.  All sites are certified, including `range` sites whose proofs the term never uses
  (`overflow`'s `error[range]`); unreached sites are swept at the end.
- **Direct holes.** A goal that is syntactically a hypothesis in scope is filled with that proof
  without asking Z3 (reason: "the goal is a hypothesis in scope") — how `safeGet`'s index and
  `concat`'s append-length obligation are discharged.  A derived obligation with no source site (an
  intermediate spread length, the `InRange` of an argument) is asked of `certify` under a synthetic
  id, and a failure is a located diagnostic.
- **Failures.** `certified` keeps the proof; `smt-only` records a `warning[uncertified]` and a
  placeholder; `failed` records the counterexample/path/reason and an `error[<kind>]`
  (`postcondition \`…\` may not hold`, `the index may be out of bounds: …`).  A missing proof leaves
  the term incomplete, so the kernel check is skipped: never a half-checked function.

## Verdicts and kernel admission

After the walk: any `failed` site ⇒ `failed`; else any `smt-only` ⇒ `smt-only`; else
`K.checkType(env, term, signature.type)` must accept the whole term, and only then is the function
added with `addDecl` as a **`def`** (same-file calls resolve, `axiomsUsed` stays `[]`).  A
non-certified function is admitted as an **`external`** (lenient mode), each caller marked in
`dependsOnUncertified`; a kernel rejection of a complete term becomes an `internal` diagnostic with
`K.formatKernelError`, and loops/recursion are `failed` with "… not implemented yet (part B)".

## The `verify()` result (for milestone 8)

`verify(path, source, opts?: { strict?, timeoutMs?, env?, readFile?, resolver?, verifyImports? })`

- `path`, `strict`, `ok` — false on any error, on a `failed`/`rejected` function, on any axiom, and
  (strict) on an `smt-only` obligation or an uncertified dependency.  `diagnostics[]` holds the
  fragment/parse and elaborator diagnostics, sorted by (file, offset, kind, message).
- `functions[]`: `{ name, exported, span, status: "certified"|"smt-only"|"failed"|"rejected",
  certified, obligations[], dependsOnUncertified[] }`, with `obligations[]` = `{ siteId, kind, span,
  text, status, reason?, path?, counterexample? }`.

- `plan[]` — one record per runtime check (nothing is injected here): `{ function, exported, kind,
  span, specText, certified, isPrecondition, isBoundaryGuard, param?, siteId? }` — guards for an
  exported function's parameters (`kind: "guard"`), one per `@pre` (`kind: "pre"`) and per `@post`
  (the tag's own text; `certified` only when every `return` certified), and one per internal site
  (`index`, `slice`, `append-length`, `range`, `pre-call`, …) with its location and text.
- `externals[]`: `{ name, file, hash, certified: true | false | "unknown" }` per imported spec
  admitted as a kernel `external`; with `verifyImports` the imported file is verified too, which
  marks callers of an uncertified import.  `axioms[]` is `[]`; `env` is the environment after the
  file, with the certified `def`s and the `external`s.

## What part B must add

- `LoopIR`: `A = stateType`, `B = resultMotive`, `m = measureType`, `step = fun s px ih hinv => if
  cond then body else rest`, `fixWf A B m step s0 p0 hinv0`; `continue` applies `ih` to the new
  state with the `invariant-preserve`/`measure-nonneg`/`measure-decrease` proofs; `loop-state` slots
  project the carried tuple; `invariant`/`loop-measure-nonneg` facts are binders.
- Recursion: `fixWf` over the function's own type, `self` calls applying `ih`, and the `pre-call`,
  `measure-nonneg` and `measure-decrease` sites.
- Locals and division in a loop: a site whose context contains a `let`-bound local cannot be
  certified as it stands (the kernel sees the local through zeta, `certify` sees an opaque atom), so
  part B must substitute each local's definition into the goal and hypotheses, or bind its facts the
  way `bindReturnValue` does; `division-spec` facts are produced on demand today and a loop whose
  invariant or measure needs `divFloorSpec` will want them recorded by the extractor.
