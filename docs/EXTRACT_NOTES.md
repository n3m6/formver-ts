# Extraction notes (milestone 5)

Untrusted layer at `src/extract/`: `fragment.ts` (fragment check, names, type mapping, IR),
`ssa.ts` (loops/`let` → local `fixWf` functions), `specs.ts` (imports parsed, never executed),
`prelude.ts` (`Math.*` as kernel definitions).  Nothing here imports `typescript`, executes user
code, or has runtime dependencies.  Diagnostics are always located and sorted; a failure inside
the layer itself becomes an `internal` diagnostic, never an exception.
## IR node shapes (`fragment.ts`)

`extractFile(path, source, opts?) → FileIR { path, source, functions, unions, importedHashes,
diagnostics }`; `StmtIR = local | assign | if | return | switch | continue | loop | expr | nop`.

- `Binder { id, name, role, type, surface?, span? }` — `type` is a kernel `Term` in the context of
  the *preceding* binders only (`shiftTerm` moves it deeper).  Roles: `type-param param in-range
  vec-len vec-elems pre hypothesis payload local loop-state loop-measure-nonneg invariant result`.
- `Slot = binder | state{state,path,name?} | payload{union,variant,payload} | result` — where a name's
  current value lives.  `deBruijnIndex(ctx, binder) = ctx.binders.length - 1 - position`;
  `project(term, path)` walks `[0]=fst`, `[1]=snd`; a `payload` slot's `slotTerm` is the `inl`/`inr`
  injection while a *field* node projects the payload variable itself.
- `ExprIR { kind, span, type, args, literal?, slot?, union?, variant?, field?, callee?, vecLength?,
  cond?, rightBinder?, projPath?, layout?, siteId?, sites, facts }` with kinds `int bool string true
  ref field length neg not add sub mul lt le gt ge eq neq and or cond inRange call projection index
  slice append object tagTest`; `length`/`vecLength` map `.length` to the vector's length, and
  `projection` extracts a part of a packed call result along `projPath`.
- `CondIR { expr, thenBinder, elseBinder, prop, thenNarrowings, elseNarrowings, tagTest?,
  thenExpr?, elseExpr? }` — one test only: `&&`/`||`/`!` conditions are desugared into nested `if`s
  (`normalizeIf`); a `switch` is a case split.
- `UnionIR { name, discriminant, variants, sumType, file, span }`, `VariantIR { tag, index, fields,
  recordType }`, `FieldIR { name, type, path, inRangePath? }`, `SignatureIR { binders,
  preconditions, result, type }`, `FunctionIR { name, signature, params, measure?, recursive, body,
  loops, sites, imports, … }`, `LoopIR` (below).

Term building: `exprTerm(ctx, e, opts?)`, `slotTerm`, `goalTerm(site, opts?)` with `TermOptions
{ result?, proofs?: ReadonlyMap<siteId, Term> }`, `ctxOfSite(site)`, `safePropTerm` (falls back to
`Unit` while a proof is missing), `renderExpr` (the text in `site.text`).
## Signature / type mapping (`buildSignature`, `buildResult`)

Parameters, in order: type parameters `(T : Type 0)`; `number x` → `(x : Int)` then
`(r_x : InRange x)`; `readonly T[] a` → `(n_a : Int)`, `(a : Vec T n_a)`, and for
`readonly number[]` also `(elems_a : (i : Int) -> (p : And (Le 0 i) (Lt i n_a)) ->
InRange (get Int n_a a i p))`; other types bind their kernel type directly.  `a.length` maps to
`n_a` (convertible with `len T n_a a`); every vector parameter also carries the `vec-bounds` fact
`0 <= n_a <= 4294967295`.  Each `@pre` tag gets its own Pi binder `pre<k> : <prop>`.

Result: `number` → `Sigma (r : Int). And (InRange r) <posts>` (`Sigma (r : Int). InRange r` with no
`@post`); `readonly T[]` → `Sigma (m : Int). And (Vec T m) <posts>` (`Sigma (m : Int). Vec T m` with
no `@post`), `result.length` being the first component.  `ResultLayout { valuePath, inRangePath,
lengthPath, vecPath, postPath }` says where each part of a packed result lives.  `@post` tags are
combined with `And`, right-nested; `@post` on a union or generic result is rejected.  A union alias
is a nested `Sum` of variant records (declaration order); a record is a nested `Sigma` over its
fields, each `number` field contributing value + `InRange` proof, terminated by `Unit`.  Only
`number` fields, two variants and one shared string-literal discriminant are accepted.

Exact `K.formatTerm` of the mapped types (asserted in `test/extract/typemap.test.ts`):

```text
clamp  : (x : Int) -> InRange x -> (lo : Int) -> InRange lo -> (hi : Int) -> InRange hi
       -> Le lo hi -> Sigma (r : Int). And (InRange r) (And (Le lo r) (Le r hi))
concat : (T : Type 0) -> (n_a : Int) -> (a : Vec T n_a) -> (n_b : Int) -> (b : Vec T n_b)
       -> Le (n_a + n_b) 4294967295 -> Sigma (m : Int). And (Vec T m) (Eq Int m (n_a + n_b))
binarySearch : (n_a : Int) -> (a : Vec Int n_a)
       -> (elems_a : (i : Int) -> (p : And (Le 0 i) (Lt i n_a)) -> InRange (get Int n_a a i p))
       -> (target : Int) -> InRange target -> Sigma (r : Int). And (InRange r)
          (And (Le (-1) r) (Lt r n_a))
```

`readonly number[]` elements: the fact at each read is `InRange (a[i])`, justified by the runtime
boundary guard (`guardIntArray`, section 6.6), which checks every element; it is carried by the
`vec-elems` binder, so milestone 7 proves it as `elems_a i p` from the `index` site's proof.
## Loops (`ssa.ts`)

`lowerLoop(host, { ast, ctx, env, rest, k, resultType, span })` is called by the statement walker
with the enclosing continuation, so the loop node absorbs everything after it.  Carried variables
are the enclosing `let`s assigned in the body (plus a `for` loop's own `let i`).  State
`A = Sigma (v0 : T0). Sigma (v1 : T1). … Unit`, component `i` at path `[1]*i + [0]`;
`B = fun (_ : A) => Invariant s -> Result`; `m = fun (s : A) => <@decreases>`; the step is
`fun (s : A) (px : Le 0 (m s)) (ih) (hinv : Invariant s) => if cond then body else rest`; the loop is
`fixWf A B m step s0 p0 hinv0 : Result`.  `loop.initSites` are `invariant-init` and
`measure-nonneg` in the enclosing context; each back edge is a `continue` node carrying `values`
(one per carried variable) plus `invariant-preserve`, `measure-nonneg` and `measure-decrease`
(`Lt (m new) (m s)`) sites.  Early `return`s are returns of the loop function.  `@invariant` and
`@decreases` are mandatory (located errors otherwise); reassignment outside a loop,
`break`/`continue`/`throw` and array mutation are rejected.  The walker duplicates the continuation
into `if` branches (no phi nodes) and rebinds an assigned name to a fresh `local` binder for the
rest of that path.  A recursive function records `measure` and `recursive`; its call sites get
`pre-call`, `measure-nonneg` and `measure-decrease`.
## Obligation sites

`ObligationSite { id, kind, span, context: Binder[], hypotheses: FactIR[], goal: ExprIR,
resultValue?, text }`, `kind ∈ post pre-call index slice append-length range measure-nonneg
measure-decrease invariant-init invariant-preserve`.  `context` is the binder list in scope
(outermost first); `hypotheses` are the propositions assumed there (`FactIR { prop, origin,
binder?, text? }`, `origin ∈ param-in-range vec-bounds pre condition invariant tag-test
element-range division-spec call-result measure field-in-range`); `goal` is a `boolean` `ExprIR`
in that context.  Milestone 6 linearizes `goal` and the hypotheses (`goalTerm(site)`); milestone 7
certifies and fills proofs (`TermOptions.proofs` keyed by `site.id` for `index`/`slice`/`append`,
`TermOptions.result` for `@post`).  A goal of `Unit` is trivially true.  Sites inside a spec (an
invariant or a measure) are not recorded in `FunctionIR.sites`.
## Prelude (`prelude.ts`)

| surface | kernel definition |
|---|---|
| `Math.max(a, b)` | `ifLe a b (_ => b) (_ => a)` |
| `Math.min(a, b)` / `Math.abs(x)` | `ifLe a b (_ => a) (_ => b)` / `ifLe 0 x (_ => x) (_ => -x)` |
| `Math.floor(e / k)` / `Math.trunc(e / k)` | `divFloor e k` / `divTrunc e k` |

`k` must be a positive integer literal (the kernel rejects anything else); `/` outside these forms
and every other `Math.*` member is a located error; `divFloorSpec`/`divTruncSpec*` are recorded as
`division-spec` facts.
## Milestone 6/7 interface

- 6: iterate `FunctionIR.sites`; build each query from `hypotheses[].prop` and `site.goal`;
  `renderExpr` supplies the text, `kind`/`span` the diagnostic kind and location.
- 7: walk `body`/`loops` with a kernel scope over `signature.binders`; resolve `Slot`s with
  `slotTerm`/`deBruijnIndex`; build `get`/`slice`/`append`/call terms with the certified proofs;
  use `layout` for packed call results and `LoopIR`'s `stateType`/`resultMotive`/`measureType` for
  `fixWf`.  Skip any function with an error inside its span.
