/**
 * Definitional equality: beta, eta (functions and pairs), delta (unfolding `Const`
 * definitions, except opaque ones), zeta (`Let`), and the built-in conversion rules of
 * the primitive registry.
 *
 * Conversion is untyped by design: the two values come from terms that are already
 * well-typed, which is what makes the structural eta rules below sound. Comparing two
 * closures applies both to a fresh variable at level `depth`; `depth` starts at the size
 * of the ambient context so that fresh levels never collide with free variables.
 *
 * Primitive ops are compared through `convArgs` when the registry provides one, and
 * otherwise argument-wise while skipping `irrelevant` positions (proof irrelevance).
 */
import { irrelevantOf, lookupPrim } from "./builtins";
import { isKnownEnv } from "./brand";
import type { Env } from "./env";
import { applyClosure, applyValue, evalTerm, fstOf, sndOf } from "./eval";
import { formEquals, formOf } from "./linear";
import type { Level, Term } from "./term";
import type { Closure, Head, NeutralValue, PrimInfo, Value } from "./value";
import { vvar } from "./value";

/** Definitional equality of two closed terms. Never throws; a kernel bug yields `false`. */
export function isConvertible(env: Env, a: Term, b: Term): boolean {
  // A fabricated environment could make anything convertible; refuse it.
  if (!isKnownEnv(env)) return false;
  try {
    return convValue(env, 0, evalTerm(env, a, []), evalTerm(env, b, []));
  } catch {
    return false;
  }
}

/**
 * Definitional equality of two values in a context of `depth` binders. `depth` must be at
 * least the number of free variables (levels) that occur in `a` and `b`.
 */
export function convValue(env: Env, depth: Level, a: Value, b: Value): boolean {
  if (a.tag === "Neutral" && b.tag === "Neutral") return convNeutral(env, depth, a, b);
  if (a.tag === "Sort" && b.tag === "Sort") return a.level === b.level;
  if (a.tag === "Pi" && b.tag === "Pi") {
    return (
      convValue(env, depth, a.domain, b.domain) &&
      convValue(env, depth + 1, applyClosure(env, a.codomain, vvar(depth)), applyClosure(env, b.codomain, vvar(depth)))
    );
  }
  if (a.tag === "Lam" && b.tag === "Lam") {
    return (
      convValue(env, depth, a.domain, b.domain) &&
      convValue(env, depth + 1, applyClosure(env, a.body, vvar(depth)), applyClosure(env, b.body, vvar(depth)))
    );
  }
  if (a.tag === "Sigma" && b.tag === "Sigma") {
    return (
      convValue(env, depth, a.first, b.first) &&
      convValue(env, depth + 1, applyClosure(env, a.second, vvar(depth)), applyClosure(env, b.second, vvar(depth)))
    );
  }
  if (a.tag === "Pair" && b.tag === "Pair") {
    // The Sigma annotations are types, so they are ignored; eta is handled below.
    return convValue(env, depth, a.first, b.first) && convValue(env, depth, a.second, b.second);
  }
  if (a.tag === "IntLit" && b.tag === "IntLit") return a.value === b.value;
  // Integer values compare by linear normal form, so `n + 0`, `0 + n` and `n` are the same
  // value, and a length written as an expression is convertible with the bare variable it
  // normalizes to. Atoms are identified by their canonical key (`linear.ts`).
  if (a.tag === "Linear" || b.tag === "Linear") {
    return formEquals(formOf(a, irrelevantOf), formOf(b, irrelevantOf));
  }
  // All certificates prove `Empty`, so any two of them are interchangeable.
  if (a.tag === "Farkas" && b.tag === "Farkas") return true;

  // Eta laws, structurally: a value of function type is either a `Lam` or neutral, and a
  // value of Sigma type is either a `Pair` or neutral.
  if (a.tag === "Lam" && b.tag === "Neutral") return etaLambda(env, depth, a.body, b);
  if (b.tag === "Lam" && a.tag === "Neutral") return etaLambda(env, depth, b.body, a);
  if (a.tag === "Pair" && b.tag === "Neutral") return etaPair(env, depth, a.first, a.second, b);
  if (b.tag === "Pair" && a.tag === "Neutral") return etaPair(env, depth, b.first, b.second, a);

  return false;
}

function etaLambda(env: Env, depth: Level, body: Closure, other: NeutralValue): boolean {
  return convValue(env, depth + 1, applyClosure(env, body, vvar(depth)), applyValue(env, other, vvar(depth)));
}

function etaPair(env: Env, depth: Level, first: Value, second: Value, other: NeutralValue): boolean {
  return convValue(env, depth, first, fstOf(other)) && convValue(env, depth, second, sndOf(other));
}

function convNeutral(env: Env, depth: Level, a: NeutralValue, b: NeutralValue): boolean {
  if (!convHead(env, depth, a.head, b.head)) return false;
  if (a.spine.length !== b.spine.length) return false;
  for (let i = 0; i < a.spine.length; i += 1) {
    if (!convValue(env, depth, a.spine[i]!, b.spine[i]!)) return false;
  }
  return true;
}

function convHead(env: Env, depth: Level, a: Head, b: Head): boolean {
  if (a.tag === "Var") return b.tag === "Var" && a.level === b.level;
  if (a.tag === "Const") return b.tag === "Const" && a.name === b.name;
  if (a.tag === "Fst") return b.tag === "Fst" && convValue(env, depth, a.pair, b.pair);
  if (a.tag === "Snd") return b.tag === "Snd" && convValue(env, depth, a.pair, b.pair);
  return (
    b.tag === "Prim" &&
    a.op === b.op &&
    a.level === b.level &&
    convPrimArgs(lookupPrim(a.op), a.args, b.args, (x, y) => convValue(env, depth, x, y))
  );
}

/**
 * Argument comparison for one primitive op: `convArgs` when the registry has one that
 * decides, otherwise position-wise while skipping `irrelevant` positions.
 */
export function convPrimArgs(
  info: PrimInfo | undefined,
  a: readonly Value[],
  b: readonly Value[],
  conv: (x: Value, y: Value) => boolean,
): boolean {
  if (a.length !== b.length) return false;
  if (info !== undefined && info.convArgs !== undefined) {
    const verdict = info.convArgs(a, b);
    if (verdict !== undefined) return verdict;
  }
  const irrelevant = info === undefined ? undefined : info.irrelevant;
  for (let i = 0; i < a.length; i += 1) {
    if (irrelevant !== undefined && irrelevant.includes(i)) continue;
    if (!conv(a[i]!, b[i]!)) return false;
  }
  return true;
}
