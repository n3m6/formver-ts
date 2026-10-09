# formver-ts

A **build-time dependent-type verifier for a small, pure subset of TypeScript**, delivered as a
Bun plugin.

You annotate pure functions with JSDoc specs. The plugin parses them with its own parser (no
TypeScript compiler at runtime), turns the specs into proof obligations, asks **Z3** (loaded
in-process through `bun:ffi`) to find a **Farkas certificate** for each valid obligation, and has
a **trusted dependent-type kernel** check the entire function — as a term — against the
dependent type its spec denotes. Nothing counts as verified until the kernel accepts it:

```ts
/**
 * @pre lo <= hi
 * @post lo <= result && result <= hi
 */
export function clamp(x: number, lo: number, hi: number): number {
  if (x < lo) return lo;
  if (x > hi) return hi;
  return x;
}
```

```console
$ bun run verify examples/pass/clamp.ts
file                    certified   smt-only     failed   rejected
examples/pass/clamp.ts          1          0          0          0
total                           1          0          0          0
axioms used: 0
1 file(s) verified
```

The same plugin runs under `bun run`, under `bun test` (preloaded) and inside `Bun.build`. It
injects **runtime checks** for anything the kernel did not certify, editing only within existing
lines so stack-trace line numbers stay exact; `NODE_ENV=production` strips certified
postconditions and internal checks while keeping exported preconditions and boundary guards.

This is an MVP demonstration, not a production system: correctness of the kernel and
faithfulness of the extraction matter more than breadth. The authoritative specification is
[`docs/INITIAL_MVP.md`](docs/INITIAL_MVP.md); the per-component design notes live in
[`docs/`](docs) (`KERNEL_NOTES`, `SYNTAX_NOTES`, `EXTRACT_NOTES`, `VC_NOTES`, `ELAB_NOTES`,
`INJECT_NOTES`, `DIFFTEST_NOTES`).

## Quick start

```sh
bun install          # devDependencies only: typescript (for `tsc --noEmit`) and @types/bun
bun run setup        # downloads Z3 5.1.0 into .z3/, verifies its SHA-256, prints the version
bun run verify       # strict verification of examples/pass; exits 0
bun run demo         # the guided 7-step walkthrough (see below)
bun test             # the test suite (kernel, syntax, extraction, VC, e2e, difftest, hygiene)
bun run typecheck    # tsc --noEmit, strict
```

`bun run verify [paths…] [--lenient]` verifies files or directories (default `examples/pass`),
prints located diagnostics and the summary table, checks that every imported declaration was
certified in its own file at the same content hash, and exits `1` on failure. It does not inject
or run anything. `bun run verify examples/fail` exits `1` and prints the expected diagnostics.

`bun run setup` fetches the pinned Z3 official release, so it is **Linux x64 only**; on any other
platform install Z3 yourself and set `DEP_VERIFY_LIBZ3=/path/to/libz3.so`. Without Z3, strict
mode refuses to run and lenient mode warns once and runtime-checks every obligation.

A cold `bun run demo` takes roughly half a minute (most of it Z3 searching for `binarySearch`'s
loop certificates); everything is cached in `.dep-verify/`, so later runs finish in well under a
second.

## A worked example: `clamp`

The spec above is read as a dependent type (this exact text is asserted in
`test/extract/typemap.test.ts`):

```text
clamp : (x : Int) -> InRange x -> (lo : Int) -> InRange lo -> (hi : Int) -> InRange hi
      -> Le lo hi -> Sigma (r : Int). And (InRange r) (And (Le lo r) (Le r hi))
```

- every `number` parameter becomes an `Int` plus an `InRange` proof (safe-integer range);
- `@pre lo <= hi` becomes the hypothesis `Le lo hi`;
- the result packs the returned `Int`, its `InRange` proof and one conjunction per `@post`.

`certified` means the kernel accepted the whole function as a term of that type. For `clamp`
that is three obligations (one `post` per `return`) and three certificates, with zero axioms.

Nothing counts as verified unless the kernel accepts it, but runtime checks are still injected
for the calls the kernel *cannot* see — every exported function is a boundary whose callers are
unknown and whose TypeScript types are erased:

```ts
import * as __dv from "<repo>/src/inject/runtime.ts";/**
 * @pre lo <= hi
 * @post lo <= result && result <= hi
 */
export function clamp(x: number, lo: number, hi: number): number { __dv.guardInt("clamp", "x", x); __dv.guardInt("clamp", "lo", lo); __dv.guardInt("clamp", "hi", hi); if (!(lo <= hi)) throw new __dv.PreconditionError("clamp", "lo <= hi", {x, lo, hi}, "examples/pass/clamp.ts:2:4");
  if (x < lo) return ((result) => { if (!(lo <= result && result <= hi)) throw new __dv.PostconditionError("clamp", "lo <= result && result <= hi", {x, lo, hi, result}, "examples/pass/clamp.ts:3:4"); return result; })(lo);
  // the other two returns are rewritten the same way
}
```

The runtime path is shortened and the second and third `return`s are replaced by a comment;
everything else is verbatim. Note that the injected import is *prepended* to line 1 and every
check is inserted inside an existing line — no newline is ever added, so the line numbers of the
original file survive (only columns shift). A violated `@pre` then points at the function's own
line in the stack trace (paths shortened here):

```console
$ bun run examples/runtime/main.ts
20
PreconditionError: safeGet: precondition `0 <= i && i < a.length` failed at examples/pass/safeGet.ts:2:4 (a = [3 elements], i = 5)
      at safeGet (examples/pass/safeGet.ts:4:177)
```

And a spec the kernel cannot prove is reported as a `file:line:col` diagnostic with a
counterexample that Z3 found (the values vary between runs):

```console
$ bun run verify examples/fail/clampNoPre.ts
examples/fail/clampNoPre.ts:5:15: error[post]: postcondition `(InRange(result) && ((lo <= result) && (result <= hi)))` may not hold
  counterexample: x = -1, lo = 0, hi = -1
```

## The annotation surface

| tag | where | meaning |
|---|---|---|
| `@pre EXPR` | function | a precondition; may mention parameters |
| `@post EXPR` | function | a postcondition; may also mention `result` |
| `@decreases EXPR` | recursive function | a non-negative integer measure that strictly decreases at every recursive call |
| `@invariant EXPR` | JSDoc directly before a `while`/`for` | the loop invariant |
| `@decreases EXPR` | JSDoc directly before a `while`/`for` | the loop's termination measure |

Multiple tags of the same kind are combined with `&&`; a tag may continue across lines (a
leading `*` is stripped); an empty tag, an `@` inside an expression, and a spec block before
any other statement are errors. The spec grammar is a quantifier-free subset of the body
grammar: integer literals, identifiers, `result`, `a.length`, `a[i]`, union field access under
narrowing, unary `-`/`!`, `+`, `-`, `*` (at least one side a literal), `Math.floor(e / k)` and
`Math.trunc(e / k)`, the comparisons `< <= > >= === !==`, `&&`, `||`, ternaries, parentheses and
the prelude built-ins. There are no quantifiers, no `==`/`!=` and no calls to user functions
inside specs.

### The accepted fragment

A function is verified when its JSDoc has at least one `@pre`, `@post` or `@decreases`. Inside
such a function:

- **Types** (annotations required on every parameter and the return type): `number` — a safe
  integer, not a float; `readonly T[]` where `T` is `number`, a generic type parameter, or a
  union alias — an array is a length-indexed vector `Vec T n`, so `a.length` is part of the
  type; generic parameters `<T>`, used only as element types; non-recursive tagged unions
  declared as `type` aliases in the same file or imported from another verified file, each
  variant an object with `readonly` fields and one shared string-literal discriminant;
  `boolean`, but only as the type of a condition.
- **Statements**: `const x = e;`; `let x = e;` reassigned only inside a `while`/`for` of the same
  function, using `x = e;`, `x += e;`, `x -= e;`, `x++;` or `x--;` as statements; `if`/`else`;
  `return e;` including early returns; `switch` on a union discriminant (exhaustive, every case
  ends in `return`, no fallthrough); and `while (c) { … }` / `for (let i = e; c; UPDATE) { … }`,
  each preceded by a JSDoc block with `@invariant` and `@decreases`.
- **Expressions**: the spec grammar, plus calls to verified functions (same file or a relative
  import), `[...a, ...b]`, `a.slice(i, j)` and object literals that construct a union variant.
- **Prelude** (mapped to kernel *definitions*, not axioms): `Math.max(a, b)` → `ifLe a b (_ => b)
  (_ => a)`, `Math.min` similarly, `Math.abs(x)` → `ifLe 0 x (_ => x) (_ => -x)`, and
  `Math.floor(e / k)` / `Math.trunc(e / k)` for a positive integer literal `k` → `divFloor` /
  `divTrunc` with their exact linear specs.

Everything else is **rejected** with a located `file:line:col` diagnostic naming the construct:
`any`, `unknown`, `as`, non-null assertions, `/` outside the floor/trunc forms, float literals,
`%`, bitwise operators, mutation of parameters or captured variables, array mutation, `throw`,
`try`, `await`, `async`, generators, `this`, classes, `new`, `==`/`!=`, closures and arrow
functions, recursive type aliases, calls to unverified functions, optional chaining, spread
outside array literals, and anything the parser does not recognise.

```console
examples/fail/rejected.ts:11:33: error[fragment]: `any` is not an accepted type in verified functions
examples/fail/offByOne.ts:5:10: error[index]: the index may be out of bounds: `((0 <= i) && (i < n_a))` may not hold
  counterexample: i = 0, n_a = 0
```

The full specification of the fragment is section 4.2 of
[`docs/INITIAL_MVP.md`](docs/INITIAL_MVP.md); the diagnostic kinds are `pre-call`, `post`,
`index`, `slice`, `append-length`, `range`, `measure-nonneg`, `measure-decrease`,
`invariant-init`, `invariant-preserve`, `fragment`, `parse`, `uncertified` and `internal`.

## How it works

```text
source ─▶ lexer + JSDoc tags ─▶ fragment parser ─▶ cross-check vs Bun.Transpiler
       ─▶ fragment check, type mapping, SSA (loops/recursion) ─▶ spec resolution (imports are
       parsed, never executed) ─▶ elaborator: a kernel term with obligation holes
       ─▶ Z3 via bun:ffi: valid? counterexample; certificate search ─▶ proof terms fill the holes
       ─▶ trusted kernel: check the whole term against the spec's type ─▶ verdict + runtime
       injection plan ─▶ same-line injection ─▶ the code Bun runs
```

Obligations arise at well-defined places, and each one is either discharged with a
kernel-checked certificate or handed to a runtime check:

| obligation | arises at |
|---|---|
| `post` | every `return` |
| `pre-call` | every call to a verified function or a built-in with preconditions |
| `index` / `slice` / `append-length` | every `a[i]` / `a.slice(i, j)` / `[...a, ...b]` |
| `range` | every arithmetic operation (the safe-integer result range) |
| `measure-nonneg`, `measure-decrease` | recursive calls and loop back-edges |
| `invariant-init`, `invariant-preserve` | loops |

Loops and local `let`s become local recursive functions over a tuple of the loop-carried state,
built with the kernel's well-founded recursion operator `fixWf`; recursion becomes a `fixWf`
application over the parameter tuple with the `@decreases` measure. `fixWf` is **opaque**: it has
no reduction rule, so conversion always terminates and callers use the function's type.

A valid obligation is more than "Z3 said `unsat`": the multipliers λ of a **Farkas certificate**
must satisfy the kernel's rule (non-negative integer multipliers per hypothesis, every atom
cancelling, a negative bound sum) *after per-row GCD tightening*. Only then is a proof term
built. Obligations Z3 proves but cannot certify this way are **`smt-only`**: they fail strict
mode and get a runtime check in lenient mode.

Results are cached per file in `.dep-verify/cache/<sha256>.json`; the key hashes the verifier
version, the mode, the file's contents and every transitively imported file's contents, so
editing an imported `@pre` invalidates its dependents.

## The trust story

**Only `src/kernel/` is trusted.** It imports nothing from outside itself, uses no Bun APIs and
no npm packages; `test/hygiene.test.ts` enforces both. Everything else — the lexer and parser,
the Bun cross-check, the fragment checker, the extractor, the elaborator, the obligation layer,
the Z3 binding and the injector — is **untrusted**. Z3 is untrusted too: it is a search engine
whose answers only become proofs when the kernel's Farkas rule accepts the certificate.

The kernel is a small dependent type theory with normalization by evaluation: universes, Pi,
Sigma, `Eq`/`J`, `Sum`/`Empty`/`Unit`, a built-in `Int` whose values are linear integer normal
forms, the primitive proposition `Le` with the Farkas certificate rule (and `Lt a b` *defined*
as `Le (a + 1) b`), length-indexed vectors `Vec A n`, `fixWf` for well-founded recursion on an
`Int` measure, and floor/trunc division by a literal divisor. A function is `certified` only
when `K.checkType` accepts its complete term; only then is it added to the environment.

Because the kernel checks a term, not your source, the trusted base is wider than the kernel —
extraction could encode a *different* function and be consistent about it. The project therefore
also relies on:

1. **the kernel**, as above;
2. **the prelude's claim** that `Math.max`, `Math.min`, `Math.abs`, `Math.floor` and
   `Math.trunc` behave like their kernel definitions on safe integers (the prelude is kept
   small and documented for exactly this reason);
3. **the faithfulness of the parse**, which is *cross-checked*: every annotated function is
   printed fully parenthesized by our own printer and accepted only if `Bun.Transpiler`'s
   normalization of that printout equals the normalization of the original text — a mismatch is
   an `internal` diagnostic and the function is rejected;
4. **the faithfulness of the elaboration**, which is *differential-tested, not proven*: for every
   certified example function, 200 seeded inputs are run through the original (with injected
   checks) and through an interpreter of the kernel term; a mismatch fails the test suite. One
   test deliberately swaps the branches of `abs`'s elaborated term to show the differential test
   catches it. This is evidence, not a proof.

The examples end with **zero axioms**: `axiomsUsed(env)` is `[]`, the CLI fails if any axiom is
used, and the prelude defines `And`, `Not`, `Lt` and `InRange` instead of assuming them. The
kernel's four *primitive lemmas* — `vecBounds`, `divFloorSpec`, `divTruncSpecNonneg` and
`divTruncSpecNeg` — are primitives trusted by fiat (no reduction rule, documented in
[`docs/KERNEL_NOTES.md`](docs/KERNEL_NOTES.md)); they are part of the kernel, not axioms.

### Strict and lenient modes, and the environment

| | `bun run verify` (CLI) | plugin (`bun run`, `bun test`, `Bun.build`) |
|---|---|---|
| default | **strict** | **lenient** |
| switch | `--lenient` | `DEP_VERIFY_STRICT=1` |
| strict means | every obligation kernel-certified; every imported declaration certified in its own file at the same content hash | same |
| `smt-only` | error (exit 1) | warning; a runtime check is injected |
| invalid obligation | error with a counterexample | warning; a runtime check is injected |

A `smt-only` obligation is one Z3 proved but the kernel did not certify; an invalid one has a
counterexample, so no runtime check can excuse it and the CLI still exits `1` under `--lenient`.

| environment variable | effect |
|---|---|
| `DEP_VERIFY_STRICT=1` | the plugin verifies strictly and rejects the import/build on failure |
| `DEP_VERIFY_LIBZ3=/path/to/libz3.so` | use this Z3 shared library instead of `.z3/` |
| `DEP_VERIFY_NO_CACHE=1` | bypass `.dep-verify/` in both directions |
| `NODE_ENV=production` | strip certified postconditions and certified internal checks (below) |

## Production builds (`NODE_ENV=production`)

| plan record | development | production |
|---|---|---|
| boundary guard of an exported parameter | keep | **keep** |
| `@pre` of an exported function | keep | **keep** |
| `@pre` of a non-exported function called from unverified code in the same file | keep | **keep** |
| `@pre` of a non-exported function whose callers are all verified | keep | drop |
| `@post` (all sites certified) | keep | drop |
| `@post` (uncertified) | keep | **keep** |
| internal obligation (certified) | keep | drop |
| internal obligation (uncertified) | keep | **keep** |

Exported functions always keep precondition checks and boundary guards, because their callers are
unknown and TypeScript types are erased at runtime; a boundary guard on `readonly number[]`
checks **every element** and is therefore O(n). `bun run demo` step 6 builds `examples/pass`
twice and counts the surviving checks in both outputs.

## Known limits

- Integer facts that have no Farkas certificate after per-row tightening (they need cutting
  planes or branch-and-bound proofs) are **smt-only**: they fail strict mode and get runtime
  checks in lenient mode.
- There is **no congruence reasoning about array elements**: `i === j` does not let the kernel
  conclude `a[i] === a[j]`.
- Specs are **quantifier-free**; there are no claims about all elements of an array.
- **Recursive data types** (lists, trees) are unsupported; tagged unions must be non-recursive.
- **`number` means a safe integer**; floats are not verifiable.
- `boolean` appears only as a condition, not as a parameter, return or `const` type.
- Exported functions always keep precondition checks and boundary guards, because their callers
  are unknown and TypeScript types are erased at runtime. Boundary guards on `readonly number[]`
  are O(n).
- The trusted base is the kernel, plus the prelude's claim that `Math.max`, `Math.min`,
  `Math.abs`, `Math.floor` and `Math.trunc` behave like their kernel definitions on safe
  integers, plus the faithfulness of our parse (checked against Bun) and elaboration
  (differential-tested, not proven).
- The bundled Z3 setup is **Linux x64 only**; other platforms set `DEP_VERIFY_LIBZ3`.
- `.tsx` files are not processed (only `.ts` and `.mts`).
- `bun:ffi` is marked experimental by Bun, and a native crash in Z3 would take the process down.

Beyond the specification's list, these limitations are visible in the current implementation.
Each is reported as a located diagnostic, never as a crash or a wrong verdict:

- **Mutual recursion** between local functions is not supported; both functions are reported
  with an `error[internal]` naming the cycle.
- A **loop-carried array/vector local** is rejected with a located `error[fragment]`: the loop
  state is a tuple of values and cannot carry the vector's length around the loop.
- A **`readonly number[]`-valued local** (`const out = a.slice(0, n)`) is rejected, because the
  kernel has no congruence rule for `get` over `slice`/`append` and so cannot derive element
  ranges for a derived array. Vector locals with a **generic** element type
  (`a: readonly T[]`) do verify and keep their length.
- **Tagged unions** are limited to **two variants** with **`number` fields** (and their `InRange`
  facts). Section 4.2 allows more; the encoding (a nested `Sum` of `Sigma` records) exists, but
  the fragment checker only builds it for that shape.
- **Union literals** (`{ kind: "a", v: x }`) are accepted where an expected union type is in
  scope — currently a `return` position — but not yet as a `const` initializer or a call
  argument. **Narrowing** works on a variable or field slot (`const u = us[0]; if (u.kind ===
  "a")`), not directly on an index expression (`if (us[0].kind === "a")`).
- **Nested loops** are rejected: a variable assigned by an outer loop cannot be updated after an
  inner loop, and the outer loop's carried state is not threaded through the inner one.
- `Math.max`, `Math.min` and `Math.abs` map to their kernel definitions (section 6.3), but the
  kernel has no dependent case rule for `ifLe` on non-literal bounds, so a **range fact about
  their result cannot be certified**: a function whose arithmetic uses them fails with
  `error[range]`. Write the branch (`x < y ? y : x`) instead — that form certifies. `Math.floor`
  and `Math.trunc` with a positive literal divisor do work, through `divFloor`/`divTrunc` and
  their spec lemmas.
- A function whose *declaration* is outside the fragment (a `boolean` return type, a missing
  return type, `async`) is reported as `rejected`, but it can be absent from the per-function
  verdict table, which lists the functions the extractor could build an IR for.

## Repository layout

```text
src/
  kernel/          TRUSTED. Terms, values, NbE, conversion, bidirectional checking, the
                   built-in Int/Le/Farkas/Vec/fixWf/division rules, environments, errors.
  syntax/          Whole-file lexer, JSDoc tags, fragment parser, parenthesised printer,
                   Bun.Transpiler cross-check.
  extract/         Fragment checker and type mapping, SSA (loops/recursion into fixWf), spec
                   resolution (imports parsed, never executed), prelude, elaborator.
  vc/              Obligation records, linear normalization and case splitting (mirroring the
                   kernel's tightening), SMT-LIB printing, the bun:ffi Z3 binding, certify.
  inject/          runtime.ts (error classes, guards, check helpers) and inject.ts (same-line
                   injection, production stripping).
  difftest/        Interpreter for erased kernel terms, seeded input generator, test driver.
  verify.ts        The per-file driver; cache.ts, plugin.ts, preload.ts, cli.ts, diagnostics.ts.
scripts/           setup-z3.ts, demo.ts (the §10 walkthrough), prove-false.ts (step 7's cases).
examples/          pass/ (certified), fail/ (one diagnostic kind each), runtime/ (the plugin).
test/              kernel/ syntax/ extract/ vc/ e2e/ difftest/ hygiene.test.ts.
docs/              INITIAL_MVP.md (the specification) and the per-milestone design notes.
```

`bun test` runs the whole suite — kernel soundness and conversion, syntax and cross-check,
extraction, obligations and Z3, end-to-end plugin/build/CLI/cache tests, differential testing
and the repository hygiene rules — and `bun run typecheck` is `tsc --noEmit` under `strict`.
`package.json` has **no runtime dependencies** (also enforced by `test/hygiene.test.ts`);
`typescript` is a devDependency used only by `tsc`, and no shipped code imports it.

## Notes on the plan and its examples

- **The examples needed no adjustment**: every file in section 8 of `docs/INITIAL_MVP.md` is
  used verbatim (`examples/fail/rejected.ts` carries a comment per construct naming the
  expected diagnostic, as the plan describes).
- Counterexample values are Z3's choice and **vary between runs**, exactly as the plan warns;
  `clampNoPre.ts` reports each of its two failing `return`s with the values Z3 happened to pick.
- A diagnostic prints the **elaborated** proposition, so a `@post` message includes the
  `InRange` conjunct (`(InRange(result) && ((lo <= result) && (result <= hi)))`) rather than the
  raw tag text, and the illustrative `path:` line of section 4.3 appears only when a case split
  produced the counterexample.
- The runtime `PreconditionError`'s `loc`/`file`/`line` fields point at the `@pre` tag's own
  location (`safeGet.ts:2:4`), while the thrown stack frame is the function's line
  (`safeGet.ts:4`) — that is the line the error is reported at, and the line numbers are exact
  because injection never adds lines.
- `examples/fail/overflow.ts` reports both `error[range]` and `error[post]`; the plan asked for
  the `range` diagnostic, which is present.
- A counterexample for a recursive function's `measure-decrease` can name Z3's atom for the
  packed argument state instead of a source variable (`counterexample: fst ?4 = 1`), because the
  measure is stated over the `fixWf` state tuple.
- The plugin skips this repository's own `src/`, **`test/` and `scripts/`** (the plan mentioned
  only `src/`): tests and fixtures deliberately contain spec-looking text.

## License

MIT — see [`LICENSE`](LICENSE).
