/**
 * Read-back: quoting semantic values to normal-form terms.
 *
 * `quote(env, depth, value)` produces a term whose free variables are the `depth`
 * enclosing binders, in order: the variable at level `l` becomes `Var (depth - 1 - l)`.
 * Quoting a `Pi`, `Sigma` or `Lam` applies its closure to a fresh variable at level
 * `depth`, which is why quoting needs the global environment.
 *
 * `normalize` is the public `quote(eval(term))`.
 */
import type { Env } from "./env";
import { err, internalError, KernelInternalError, ok, type KernelError, type Result } from "./errors";
import { applyClosure, evalTerm } from "./eval";
import { type Level, type Term, app, constTerm, farkasTerm, intLit, lam, pair, pi, primTerm, sigma, sort, varTerm } from "./term";
import type { Head, Value } from "./value";
import { vvar } from "./value";

export function quote(env: Env, depth: Level, value: Value): Term {
  switch (value.tag) {
    case "Sort":
      return sort(value.level);
    case "IntLit":
      return intLit(value.value);
    case "Pi":
      return pi(
        value.name,
        quote(env, depth, value.domain),
        quote(env, depth + 1, applyClosure(env, value.codomain, vvar(depth))),
      );
    case "Lam":
      return lam(
        value.name,
        quote(env, depth, value.domain),
        quote(env, depth + 1, applyClosure(env, value.body, vvar(depth))),
      );
    case "Sigma":
      return sigma(
        value.name,
        quote(env, depth, value.first),
        quote(env, depth + 1, applyClosure(env, value.second, vvar(depth))),
      );
    case "Pair":
      return pair(
        quote(env, depth, value.sigma),
        quote(env, depth, value.first),
        quote(env, depth, value.second),
      );
    case "Farkas":
      return farkasTerm(value.hyps, value.coeffs);
    case "Neutral": {
      let out = quoteHead(env, depth, value.head);
      for (const arg of value.spine) out = app(out, quote(env, depth, arg));
      return out;
    }
  }
}

function quoteHead(env: Env, depth: Level, head: Head): Term {
  switch (head.tag) {
    case "Var": {
      const index = depth - 1 - head.level;
      if (index < 0) {
        throw new KernelInternalError(
          `quoting a value with a free variable at level ${head.level} in a context of ${depth} binders`,
        );
      }
      return varTerm(index);
    }
    case "Const":
      return constTerm(head.name);
    case "Prim":
      return primTerm(
        head.op,
        head.args.map((arg) => quote(env, depth, arg)),
        head.level,
      );
    case "Fst":
      return { tag: "Fst", pair: quote(env, depth, head.pair) };
    case "Snd":
      return { tag: "Snd", pair: quote(env, depth, head.pair) };
  }
}

/** `quote(eval(term))`: the definitional normal form of a term. */
export function normalize(env: Env, term: Term): Result<Term, KernelError> {
  try {
    return ok(quote(env, 0, evalTerm(env, term, [])));
  } catch (cause) {
    return err(internalError(cause));
  }
}
