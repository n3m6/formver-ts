# Parser and semantics probes

formver-ts verifies its own parse of the source, cross-checked against `Bun.Transpiler`. If that
parse, or the meaning given to it, differs from what Bun runs, the proof is about a different
program. Each probe is a small program whose correctness hinges on one JavaScript corner case.
It is labeled with what correct semantics require: `expect: reject` probes break their spec, so
certifying one is unsound; `expect: certify` probes are correct, so rejecting one is only
incomplete.

## Sub-features

- `probe-asi`: `asi-return` (`return` then a newline returns `undefined`).
- `probe-precedence`: `sub-assoc`/`sub-assoc-ok`, `ternary-assoc`/`ternary-assoc-ok`, `minus-minus`, `compare-chain` (`a < b < c`), `comma-operator`.
- `probe-lexing`: `comment-trap`/`comment-trap-ok`, `hex-literal` (`0x10`), `separator-literal` (`1_000`), `exponent-literal` (`1e3`).
- `probe-scoping`: `shadow`/`shadow-ok` (a block `const` shadowing a parameter), `default-param`.
- `probe-control`: `switch-fallthrough`.
- `probe-numeric-model`: `float-rounding` (`x + 2 - 2` at `2^53 - 1`), `floor-trunc`/`floor-ok`, `div-zero`, `math-max-empty`.
- `probe-spec-reading`: `multi-post-first` and `multi-post-last` (every postcondition counts), `union-rect` (union field access), `spec-index` (`a[i]` inside a postcondition).
- `probe-neq-branch`: `neq-else`, `neq-ternary` and `neq-call` (code reached when an `x !== y` condition is false), with `neq-ok` as the control. **These three are `SOUNDNESS-BUG` at `8135f5b`**; see Gotchas.
- `probe-injection`: `comma-operator` also checks that the plugin's injected code leaves the return value alone. **`INJECTION-BUG` at `8135f5b`**; see Gotchas.

## How to get to it (user POV)

- Any user file containing these constructs, verified with `bun run verify` or loaded through
  the plugin. `run-probes.sh` drives the CLI on copies of `probes/*.ts`.

## Driving it with the soundness tools

Preconditions:

- The baseline preconditions in `README.md` hold, and `$RUN` exists.

- **All probes.** Run `$SK/capture.sh "$RUN" parser-probes.all -- $SS/run-probes.sh "$RUN"`. It takes about 6 s. On a correct verifier it exits 0: every `expect: reject` probe is `ok` with at least one oracle `VIOLATION` (proof that the probe really is wrong), and every `expect: certify` probe is `ok` or `incomplete`.
  - Observed at commit `8135f5b`: `ok=23 incomplete=3 SOUNDNESS-BUG=3 INJECTION-BUG=1`, exit 1.
  - `SOUNDNESS-BUG`: `neq-else`, `neq-ternary`, `neq-call`.
  - `INJECTION-BUG`: `comma-operator`.
  - `incomplete`: `shadow-ok`, `ternary-assoc-ok`, `spec-index`.
  - Until those bugs are fixed, that exact line is the baseline. Any other change is news.
- **One probe.** Run `$SS/run-probes.sh "$RUN" hex-literal` and read `$RUN/evidence/probes/hex-literal.verify.log` (the verifier's diagnostics) next to `hex-literal.oracle.log` (the concrete violation).
- **Add a probe.** Write `probes/<name>.ts` with line 1 `// expect: reject` or `// expect: certify`, then a comment saying which JavaScript rule decides it. Bound every parameter in the precondition (`-1000 <= x && x <= 1000`) so range obligations do not mask the behavior under test. Add `// oracle: none` only when fuzzing cannot show the defect. Then run it by name. A new `expect: reject` probe must come back with oracle `VIOLATION`; otherwise it is `CHECK-PROBE` and proves nothing.

## Gotchas

- **Open soundness bug (`!==` conditions).** At `8135f5b`, whatever runs when an `x !== y`
  condition is false (the `else` branch, the code after an `if (x !== y) return`, or the second
  arm of `x !== y ? a : b`) is elaborated under contradictory hypotheses, so any claim there is
  "certified". `ifLeOperands` maps `neq` to `[lhs + 1, rhs]` in `src/extract/elaborate.ts`
  (around line 3351) and `src/extract/fragment.ts` (around line 988), but the eq/neq caller
  expects `[lhs, rhs]`, so the "equal" arm assumes `lhs + 1 = rhs` as well as `lhs = rhs`. The
  forms `!(x === y)` and `x === y` with an `else` are handled correctly. No shipped example uses
  `!==` in a condition, so `test/difftest` never reached it.
- **Open injection bug (comma in `return`).** The postcondition wrapper
  (`src/inject/inject.ts`, around line 443) splices the return expression into
  `((result) => { … })(<expr>)`. Expression extents exclude their own parentheses, so
  `return (x, 0)` becomes a call with two arguments: it returns `x` instead of `0`, and the
  injected `result === x` check passes on the wrong value. The comma operator is already a
  fragment error, so only lenient mode runs this code.
- `spec-index` is rejected with an internal-sounding message (`the term for \`index\` needs the
  proof of obligation site #N; pass it in TermOptions.proofs`), although the README's spec
  grammar lists `a[i]`. The function then vanishes from the verdict table, the CLI adds
  `no annotated function to verify`, and the lenient plugin injects no checks at all (see
  `rt-lenient-unextracted` in `verify-formver`).

- Many `expect: reject` probes are refused as `error[fragment]` (ASI, comma, `a < b < c`,
  default parameters, `switch` fall-through, `Math.max()`, division by zero, `1e3`). That is
  correct; they still guard against a future fragment extension that accepts the construct and
  gets its meaning wrong.
- `shadow-ok` and `ternary-assoc-ok` are rejected because a `?:` whose branches are
  propositions, inside a postcondition, is "outside the SMT encoding" (located `error[post]`).
  This is a completeness gap, and the README's known limits do not list it yet.
- A paired `-ok` probe shows that the verifier can still prove the correct version. Without it,
  a verifier that rejects everything passes every `reject` probe.
- `// @ts-ignore` lines in two probes only silence `tsc`. Bun and the verifier never read
  them as specs.
- `union-rect` uses `union-rect.gen.ts` automatically, because the runner passes `--gen` when a
  same-named `.gen.ts` exists.
