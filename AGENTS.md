# AGENTS.md

formver-ts (`dep-verify`) is a build-time dependent-type verifier for a small, pure subset of
TypeScript, shipped as a Bun plugin. JSDoc specs (`@pre`, `@post`, `@decreases`, `@invariant`)
become proof obligations; Z3 (via `bun:ffi`) searches for Farkas certificates; a trusted kernel
checks the whole function as a term. `README.md` is the user-facing overview,
`docs/INITIAL_MVP.md` is the authoritative specification, and `docs/*_NOTES.md` hold the
per-component design notes. Read the relevant notes before changing a component.

## Commands

```sh
bun install          # devDependencies only
bun run setup        # pinned Z3 into .z3/ (Linux x64; elsewhere set DEP_VERIFY_LIBZ3)
bun run verify [paths…] [--lenient]   # strict CLI, default examples/pass
bun test             # full suite, ~95 s cold; `bun test test/kernel` etc. for a subset
bun run typecheck    # tsc --noEmit, strict
bun run demo         # 7-step self-checking walkthrough
```

Before claiming a change is done, run `bun run typecheck` and `bun test`, and
`bun run verify` must still exit 0 on `examples/pass` with `axioms used: 0`. Use
`DEP_VERIFY_NO_CACHE=1` when checking verifier behavior: a warm `.dep-verify/` cache answers
instantly and proves nothing about the current code.

## Trust boundary (hard rules)

- **Only `src/kernel/` is trusted.** It imports nothing outside itself, uses no Bun APIs, no npm
  packages and no ambient host globals. `test/hygiene.test.ts` enforces this; never weaken the
  hygiene checker to make a change pass.
- Code outside the kernel imports kernel code only through `src/kernel/index.ts`.
- `package.json` has no runtime dependencies, and the only devDependencies are `typescript` and
  `@types/bun`. No shipped code imports `typescript`.
- Nothing is `certified` unless `K.checkType` accepts the complete term. Never downgrade a
  kernel rejection, treat Z3 `unsat` as a proof, or add axioms; the examples use zero axioms and
  the CLI fails if any is used.
- Untrusted layers (syntax, extract, vc, inject, Z3) must fail closed: anything unrecognised is a
  located `file:line:col` diagnostic (`fragment`, `parse`, `internal`, …), never a crash or a
  wrong verdict.
- Injected runtime checks never add lines; they are inserted within existing lines so stack-trace
  line numbers stay exact.

## Layout

- `src/kernel/` trusted type theory (NbE, conversion, Int/Le/Farkas, Vec, `fixWf`, division).
- `src/syntax/` lexer, JSDoc tags, fragment parser, printer, `Bun.Transpiler` cross-check.
- `src/extract/` fragment check, type mapping, SSA, spec resolution, prelude, elaborator.
- `src/vc/` obligations, linear normalization, SMT-LIB, Z3 binding, certificate search.
- `src/inject/` same-line runtime-check injection and the runtime helpers.
- `src/difftest/` interpreter for kernel terms and seeded differential tests.
- `src/verify.ts` per-file driver; `cache.ts`, `plugin.ts`, `preload.ts`, `cli.ts`.
- `examples/pass/` must certify; `examples/fail/` must produce its diagnostics. Both are used
  verbatim from the spec and by tests and the demo: don't edit them to make something pass.
- `test/` mirrors `src/`; e2e fixtures live in `test/e2e/fixtures/`.

The preload plugin (`bunfig.toml`) skips this repo's `src/`, `test/` and `scripts/`, so a
program meant to be verified by the plugin must live elsewhere (for example `examples/` or a
temp directory).

## Conventions

- TypeScript under `strict`, ESM, Bun APIs outside the kernel. Match the surrounding style:
  module-level doc comments that cite the specification section, named exports, no `any`.
- Diagnostics quote the user's spec text where one exists and always carry a source span.
- When adding a fragment feature, update the fragment checker, the elaborator, the
  differential-test interpreter if needed, tests in the matching `test/` subdirectory, and the
  README's fragment and known-limits sections.
- Commit messages start with the component: `Kernel: …`, `Extraction: …`, `Elaboration/VC: …`,
  `Pipeline: …`, `Diagnostics: …`, `README: …`.

## Skills

- `.agents/skills/verify-formver/` drives the real surfaces (CLI, plugin, `Bun.build`, cache)
  and captures transcripts. Use it after changing `src/`, `scripts/` or `examples/`.
- `.agents/skills/verify-formver-soundness/` red-teams soundness (mutants, independent oracle,
  parser probes, kernel attacks). Use it after any change to `src/kernel`, `src/vc`,
  `src/extract`, `src/syntax`, `src/verify.ts` or the elaborator.
