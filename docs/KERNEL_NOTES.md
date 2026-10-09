# Kernel notes (milestone 3)

Trusted core in `src/kernel/`: it imports only from inside that directory (no Bun APIs, no
npm packages, no `console`). The public surface is `src/kernel/index.ts`. The prelude has
**zero axioms** (`axiomsUsed(emptyEnv()) === []`): `And`, `Not`, `Lt`, `InRange` are
definitions inserted through `addDecl`.

## Terms, values, eval, quote

- `Term` is specification 6.1.1; binding is by de Bruijn index, `Scope`/`Mk` build terms
  without index arithmetic (`mk`, `piMk`, `lamMk`, `appMk`, `primMk`, `farkasMk`, ...).
- `Value = Sort | Pi | Lam | Sigma | Pair | IntLit | Linear | Farkas | Neutral`. Value
  environments are indexed by de Bruijn **level**, so levels are globally fresh; `Closure`
  is a body term plus the environment it was created in.
- Milestone 3 adds `Linear` (`value.ts`): `{ tag, k, atoms: Map<key, {key, coefficient,
  repr}> }` with no zero coefficients, built by `vlinear` (which returns `IntLit` when no
  atom is left). `repr` is a representative value for the atom, used only by `quote`.
- `quote` reads a `Linear` back as `k + Σ cᵢ·rᵢ` (`mulConst` for `cᵢ ≠ 1`), so types that
  mention a linear length survive quoting and re-evaluation. A form that is a single atom
  with coefficient 1 quotes as that atom.
- `erase` is unchanged; there is no runtime content in a linear value (it only appears
  inside `Int`-typed arguments of built-ins).

## The registry (`builtins.ts`)

`PRIMS: Record<PrimOp, PrimInfo>` (frozen) plus `lookupPrim`/`irrelevantOf`.
`PrimInfo = { name, arity, typeFor(level), reduce?, irrelevant?, convArgs?,
positiveLiteralArgs? }`.

- `typeFor(level)` is a closed Pi telescope; `check.ts` walks it, checking each argument
  against the domain and substituting into the codomain. Prims must be **fully applied**
  (`prim-arity` otherwise), which is why `fixWf` always appears with all six arguments.
- `reduce(args, ctx)` returns `Value | undefined`; `undefined` means stuck. No `reduce`
  means opaque: `fixWf` never unfolds, so conversion terminates.
- `irrelevant` lists 0-based proof-argument positions ignored by conversion **and** by
  atom keys. Masks: `get[4]`, `append[5]`, `slice[5]`, `castVec[3]`, `intEq[2,3]`,
  `byContra[2]`, `fixWf[5]`, `divTruncSpecNonneg[2]`, `divTruncSpecNeg[2]`.
  `ifLe`'s branches are **not** irrelevant: the result is a value of the motive, not a
  proof.
- `convArgs` overrides argument comparison; only `Le` has one.
- `positiveLiteralArgs` (milestone 3's one hook) lists positions that must be a positive
  integer literal *term*; `check.ts` enforces it with `prim-not-literal`. Used by
  `divFloor[1]`, `divFloorSpec[1]`, `divTrunc[1]` and both `divTruncSpec*[1]`.

Ops: `Empty, Unit, tt, Sum, inl, inr, case, absurd, Eq, refl, J, Int, add, sub, neg,
mulConst, Le, ifLe, byContra, intEq, Vec, len, vecBounds, get, append, slice, castVec,
fixWf, divFloor, divFloorSpec, divTrunc, divTruncSpecNonneg, divTruncSpecNeg`.

Primitive **lemmas** (a type, no reduction rule, no implementation; trusted by fiat and
documented): `vecBounds`, `divFloorSpec`, `divTruncSpecNonneg`, `divTruncSpecNeg`. They are
prims, never `axiom` declarations. Their soundness rests on the divisor-literal hook and on
the fact that only `append`/`slice`/`castVec` build vectors.

## Linear forms and atom keys (`linear.ts`)

- `LinearForm = { k: bigint, atoms: Map<key, LinearAtom> }`; `formOf(value)` maps an
  `Int` value to its form (`IntLit`/`Linear` directly, anything else becomes one atom),
  `vform` goes back, and `formAdd`/`formSub`/`formNeg`/`formScale`/`formEquals` do the
  arithmetic. `gcd`/`floorDiv`/`truncDiv` live here too.
- `keyOfValue(value)` is the canonical key, computed **structurally**, never by quoting at
  an ambient depth: free variables are named by their (globally fresh) level, closure
  bodies are read back with traversal-relative de Bruijn indices (alpha-invariant), proof
  arguments are erased, `Farkas` values all key as `Proof`, `Pair` annotations are ignored,
  and a form that is one atom with coefficient 1 and constant 0 keys as that atom. Names
  and op tags are length-prefixed, so equal keys mean convertible atoms and distinct keys
  never merge distinct values.
- Two values with the same key are therefore interchangeable for `Le` conversion; keys
  that *differ* for convertible values only lose completeness, never soundness.

## Conversion (`conv.ts`)

- `IntLit`/`Linear`/neutral `Int` values compare by linear form (so `n + 0 ≡ 0 + n ≡ n`,
  `n - n ≡ 0`, `2·x ≡ x + x`).
- `Le a b ≅ Le c d` iff the forms of `b - a` and `d - c` are equal (`convArgs`). That is
  what lets `Lt a b` (the definition `Le (a+1) b`) and the `no` branch of `ifLe (x+1) lo`
  be used where `Le lo x` is expected.
- `Vec A n ≅ Vec A m` follows from the `Int` rule on the length argument, so no `Vec`
  `convArgs` is needed.
- Everything else is unchanged: beta, eta for functions and pairs, delta (except opaque),
  zeta, and position-wise comparison skipping `irrelevant` positions.

## Farkas (`farkas.ts`)

- `Row = { a: Record<string, bigint>, b: bigint }` means `Σ aᵢ·xᵢ <= b`. A hypothesis of
  type `Le s t` gives the row of the linear form of `s - t`: coefficients `cᵢ`, bound
  `b = -k` where `k` is that form's constant (`Lt` is already `Le` by evaluation). Row
  building lives in `rowOfLe(value)`; the WHNF must be a saturated `Le`, otherwise
  `farkas-not-a-le-hypothesis`.
- `tightenRow(row)` (GCD of the non-zero coefficients, `b := floor(b/g)`) and
  `checkCertificate(rows, coeffs)` (non-negative multipliers, every atom cancels, negative
  bound) are **frozen**: `src/vc/linear.ts` duplicates them in milestone 6.
- `checkFarkas({ hypTypes: Value[], coeffs })` takes the hypotheses' inferred types as
  *values* (that is what `check.ts` has). Its result is `Empty`.
- `ifLe` on literal bounds reduces by selecting a branch and handing it
  `byContra x y (fun k => Farkas [k] [1])`; `leProofTerm(x, y)` builds that proof, and
  `K.LeProof x y` exposes it for literal `x <= y`.

## What milestone 4+ can rely on

- Build terms with `IfLe`, `ByContra`, `LeProof`, `IntEq`, `Len`, `VecBounds`, `Get`,
  `Append`, `Slice`, `CastVec`, `FixWf`, `DivFloor`/`DivFloorSpec`,
  `DivTrunc`/`DivTruncSpecNonneg`/`DivTruncSpecNeg`, `Lt`, `Add`/`Sub`/`Neg`/`MulConst`.
- `K.SAFE_MAX` (2^53-1) and `K.MAX_VEC_LEN` (4294967295) are the prelude's bounds.
- A divisor that is not a positive literal term is rejected with `prim-not-literal`; a
  non-literal `mulConst` multiplier is simply stuck and treated as an opaque atom.
- Invariants to preserve: no `Type l : Type l`; `fixWf` never unfolds; conversion never
  identifies `Vec A n` with `Vec A (n+1)`, `2·x` with `x+1`, or `Le a b` with
  `Le a (b+1)`; `conv.ts`'s eta rules assume convertible types, so never call `convValue`
  on ill-typed values.
