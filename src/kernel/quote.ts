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
import { OP_ADD, OP_MUL_CONST } from "./builtins";
import { type Level, type Term, app, constTerm, farkasTerm, intLit, lam, pair, pi, primTerm, sigma, sort, varTerm } from "./term";
import type { Head, LinearForm, Value } from "./value";
import { vvar } from "./value";

export function quote(env: Env, depth: Level, value: Value): Term {
  switch (value.tag) {
    case "Sort":
      return sort(value.level);
    case "IntLit":
      return intLit(value.value);
    case "Linear":
      return quoteLinear(env, depth, value);
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

/**
 * Reads a linear value back as a term: `k + Σ cᵢ · rᵢ`, where each `rᵢ` is the quoted
 * representative of an atom and `cᵢ * rᵢ` is `mulConst cᵢ rᵢ`. Evaluating the result gives
 * a linear value with the same constant and the same atom keys, so quoting a type that
 * mentions a linear length never loses information. A single atom with coefficient 1 and
 * constant 0 is quoted as the atom itself.
 */
function quoteLinear(env: Env, depth: Level, value: LinearForm): Term {
  const atoms = [...value.atoms.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
  const only = atoms.length === 1 ? atoms[0]![1] : undefined;
  if (value.k === 0n && only !== undefined && only.coefficient === 1n) {
    return quote(env, depth, only.repr);
  }
  let out: Term = intLit(value.k);
  for (const [, atom] of atoms) {
    const repr = quote(env, depth, atom.repr);
    const term = atom.coefficient === 1n ? repr : primTerm(OP_MUL_CONST, [intLit(atom.coefficient), repr]);
    out = primTerm(OP_ADD, [out, term]);
  }
  return out;
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
