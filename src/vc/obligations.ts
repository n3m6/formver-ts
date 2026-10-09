/**
 * The obligation record (specification 6.4/6.5), the interface milestone 7 hands to
 * `certify`.
 *
 * An obligation is a proposition to prove, a set of propositional hypotheses in scope, and
 * the location and kind a diagnostic would carry. Everything in it is a *kernel term* in
 * the same ambient context — the context the elaborator is already inside — so the proof
 * `certify` returns can be dropped straight into the hole:
 *
 *     const result = certify(env, obligation);
 *     if (result.status === "certified") hole = result.proof!;   // : obligation.goal
 *
 * ## Ordering
 *
 * `hypotheses` is ordered: the multipliers of the Farkas certificate index exactly this
 * list, and the proof term is built from the same order. Reordering the list changes the
 * certificate, so the caller must keep it stable between asking for a certificate and using
 * it (which `certify` does internally).
 *
 * ## Proof terms for the hypotheses
 *
 * The rows of a certificate come from the hypotheses' *propositions*; the kernel's
 * `Farkas` term needs a *proof term* for each of them, in the same order. Two ways to
 * supply those:
 *
 *   - `proofs[i]`: the proof term of `hypotheses[i]` in the ambient context. This is the
 *     only way to name a compound proof (for example `elems_a i p`, the element-guard
 *     application the extractor carries for `readonly number[]`);
 *   - `context`: the types of the ambient binders, outermost first. Then `certify` looks up
 *     each hypothesis proposition among the binders and uses the matching variable. This is
 *     the natural thing for the elaborator, whose hypotheses usually *are* binders.
 *
 * When both are missing, the fallback is the "innermost binders" convention: the hypotheses
 * are assumed to be the innermost binders of the ambient context, in the given order, so
 * `hypotheses[i]` has proof `Var (n - 1 - i)`. That keeps the record usable on its own (and
 * is what the tests use), but real callers should supply `proofs` or `context`.
 *
 * ## Atom names
 *
 * `atomNames` maps a kernel atom key (`K.keyOfValue`'s string, for example `Var(7)`) to the
 * name a user would recognise (`x`). It is used only to report a counterexample. Note that
 * a binder's level is its position from the *inside* of the context: the outermost of `d`
 * binders has level `d - 1`, hence key `Var(d - 1)`. `contextAtomNames` builds the whole
 * map from binder names.
 */
import * as K from "../kernel/index";
import type { DiagnosticKind, Span } from "../diagnostics";

export interface Obligation {
  /** Stable identity of the source site, for diagnostics and the cache. */
  readonly id: string;
  /** The section 4.3 diagnostic kind: `post`, `index`, `range`, … */
  readonly kind: DiagnosticKind;
  readonly span: Span;
  /**
   * The propositions assumed at this site, in order. Each is a `Term` of type `Type 0`;
   * the certificate multipliers index this exact list.
   */
  readonly hypotheses: readonly K.Term[];
  /** The proposition to prove, in the same ambient context. */
  readonly goal: K.Term;
  /** Atom key -> user-facing name, for counterexample reporting. */
  readonly atomNames?: Readonly<Record<string, string>>;
  /**
   * One proof term per hypothesis, in the same order, in the ambient context. Optional:
   * see the module comment for the fallbacks.
   */
  readonly proofs?: readonly K.Term[];
  /**
   * The ambient binder types, outermost first. Optional, but it makes atom keys exact (the
   * caller's `atomNames` and this module then agree by construction) and lets `certify`
   * look up hypothesis proofs by proposition.
   */
  readonly context?: readonly K.Term[];
}

/** The number of ambient binders an obligation's terms live under. */
export function obligationDepth(obligation: Obligation): number {
  if (obligation.context !== undefined) return obligation.context.length;
  let depth = 0;
  const note = (term: K.Term): void => {
    depth = Math.max(depth, maxFreeIndex(term) + 1);
  };
  for (const hypothesis of obligation.hypotheses) note(hypothesis);
  note(obligation.goal);
  for (const proof of obligation.proofs ?? []) note(proof);
  return depth;
}

/**
 * The largest de Bruijn index free in `term`; `-1` for a closed term. (A local copy of
 * `linear.ts`'s helper so this module stays dependency-free for callers that only build
 * records.)
 */
function maxFreeIndex(term: K.Term): number {
  let max = -1;
  const visit = (t: K.Term, depth: number): void => {
    switch (t.tag) {
      case "Var":
        if (t.index >= depth) max = Math.max(max, t.index - depth);
        return;
      case "Sort":
      case "IntLit":
      case "Const":
        return;
      case "Pi":
      case "Lam":
        visit(t.domain, depth);
        visit(t.body, depth + 1);
        return;
      case "Sigma":
        visit(t.first, depth);
        visit(t.second, depth + 1);
        return;
      case "App":
        visit(t.fn, depth);
        visit(t.arg, depth);
        return;
      case "Pair":
        visit(t.sigma, depth);
        visit(t.first, depth);
        visit(t.second, depth);
        return;
      case "Fst":
      case "Snd":
        visit(t.pair, depth);
        return;
      case "Let":
        visit(t.type, depth);
        visit(t.value, depth);
        visit(t.body, depth + 1);
        return;
      case "Prim":
        for (const arg of t.args) visit(arg, depth);
        return;
      case "Farkas":
        for (const hypothesis of t.hyps) visit(hypothesis, depth);
        return;
    }
  };
  visit(term, 0);
  return max;
}

/**
 * The fallback proof terms: `hypotheses[i]` is the innermost binder `Var (n - 1 - i)`, i.e.
 * the hypotheses were bound in order after everything else.
 */
export function innermostProofs(count: number): K.Term[] {
  const proofs: K.Term[] = [];
  for (let index = 0; index < count; index += 1) proofs.push(K.varTerm(count - 1 - index));
  return proofs;
}

/**
 * The `atomNames` map for a context of `depth` binders whose source names are `names`
 * (outermost first). The binder at position `p` is bound at level `p`, so its atom key is
 * `Var(p)` — levels are assigned in binding order, which is why the outermost binder has
 * the *lowest* level even though it has the *highest* de Bruijn index.
 */
export function contextAtomNames(
  depth: number,
  names: readonly (string | undefined)[],
): Record<string, string> {
  const out: Record<string, string> = {};
  for (let position = 0; position < depth; position += 1) {
    const name = names[position];
    if (name === undefined) continue;
    out[K.keyOfValue(K.vvar(position), K.irrelevantOf)] = name;
  }
  return out;
}

/** A `file:line:col` prefix for diagnostics and error messages. */
export function obligationLocation(obligation: Obligation): string {
  return `${obligation.span.file}:${obligation.span.line}:${obligation.span.col}`;
}
