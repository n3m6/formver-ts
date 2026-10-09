/**
 * Evaluation (normalization by evaluation).
 *
 * `evalTerm` maps a term to a semantic value. Beta and delta are performed eagerly, so
 * values come out weak-head normalized. Value environments are indexed by de Bruijn
 * *level*: `env[i]` is the value of the variable at level `i`, so `Var n` (an index)
 * reads `env[env.length - 1 - n]`. Fresh variables are created at level `env.length`,
 * which is what makes the levels used by `conv.ts` globally fresh.
 */
import { lookupPrim } from "./builtins";
import type { Env } from "./env";
import { KernelInternalError } from "./errors";
import type { Term } from "./term";
import type { Closure, GlobalInfo, NeutralValue, ReduceCtx, Value } from "./value";
import {
  extendSpine,
  vconst,
  vfarkas,
  vfst,
  vint,
  vlam,
  vpair,
  vpi,
  vprim,
  vsigma,
  vsnd,
  vsort,
} from "./value";

export function evalTerm(env: Env, term: Term, vs: readonly Value[]): Value {
  switch (term.tag) {
    case "Var": {
      const slot = vs.length - 1 - term.index;
      if (slot < 0 || slot >= vs.length) {
        throw new KernelInternalError(
          `evaluation reached a free variable: index ${term.index} with ${vs.length} binders in scope`,
        );
      }
      return vs[slot]!;
    }
    case "Sort":
      return vsort(term.level);
    case "Pi":
      return vpi(term.name, evalTerm(env, term.domain, vs), closureOf(term.name, term.body, vs));
    case "Lam":
      return vlam(term.name, evalTerm(env, term.domain, vs), closureOf(term.name, term.body, vs));
    case "App":
      return applyValue(env, evalTerm(env, term.fn, vs), evalTerm(env, term.arg, vs));
    case "Sigma":
      return vsigma(term.name, evalTerm(env, term.first, vs), closureOf(term.name, term.second, vs));
    case "Pair":
      return vpair(
        evalTerm(env, term.sigma, vs),
        evalTerm(env, term.first, vs),
        evalTerm(env, term.second, vs),
      );
    case "Fst":
      return fstOf(evalTerm(env, term.pair, vs));
    case "Snd":
      return sndOf(evalTerm(env, term.pair, vs));
    case "Let":
      // Zeta: the bound variable is replaced by the value, eagerly.
      return evalTerm(env, term.body, [...vs, evalTerm(env, term.value, vs)]);
    case "Const":
      return evalConst(env, term.name);
    case "IntLit":
      return vint(term.value);
    case "Prim":
      return evalPrim(env, term.op, term.level ?? 0, term.args, vs);
    case "Farkas":
      return vfarkas(term.hyps, term.coeffs);
  }
}

const closureOf = (name: string, body: Term, env: readonly Value[]): Closure => ({ name, body, env });

/** Applies a closure: the body is evaluated with the argument at the next level. */
export function applyClosure(env: Env, closure: Closure, arg: Value): Value {
  return evalTerm(env, closure.body, [...closure.env, arg]);
}

/** Applies a function value: beta for a `Lam`, spine extension for a neutral. */
export function applyValue(env: Env, fn: Value, arg: Value): Value {
  if (fn.tag === "Lam") return applyClosure(env, fn.body, arg);
  if (fn.tag === "Neutral") return extendSpine(fn, arg);
  throw new KernelInternalError(`cannot apply a value of kind ${fn.tag}`);
}

/** `fst p`: the projection, or a stuck projection of a neutral pair. */
export function fstOf(value: Value): Value {
  if (value.tag === "Pair") return value.first;
  if (value.tag === "Neutral") return vfst(value);
  throw new KernelInternalError(`cannot take fst of a value of kind ${value.tag}`);
}

/** `snd p`: the projection, or a stuck projection of a neutral pair. */
export function sndOf(value: Value): Value {
  if (value.tag === "Pair") return value.second;
  if (value.tag === "Neutral") return vsnd(value);
  throw new KernelInternalError(`cannot take snd of a value of kind ${value.tag}`);
}

function evalConst(env: Env, name: string): Value {
  const decl = env.decls.get(name);
  // Delta: unfold definitions, except opaque ones. Axioms and externals are opaque
  // because they have no definition at all.
  if (decl !== undefined && decl.kind === "def" && decl.opaque !== true) {
    return evalTerm(env, decl.value, []);
  }
  return vconst(name);
}

function evalPrim(
  env: Env,
  op: string,
  level: number,
  args: readonly Term[],
  vs: readonly Value[],
): Value {
  const info = lookupPrim(op);
  const values = args.map((arg) => evalTerm(env, arg, vs));
  if (info !== undefined && info.reduce !== undefined && values.length === info.arity) {
    const reduced = info.reduce(values, reduceCtx(env));
    if (reduced !== undefined) return reduced;
  }
  return vprim(op, level, values);
}

/** What a primitive reduction rule may ask of the evaluator. */
export function reduceCtx(env: Env): ReduceCtx {
  return {
    apply: (fn, arg) => applyValue(env, fn, arg),
    evalIn: (term, vs) => evalTerm(env, term, vs),
    lookup: (name) => globalInfo(env, name),
  };
}

export function globalInfo(env: Env, name: string): GlobalInfo | undefined {
  const decl = env.decls.get(name);
  if (decl === undefined) return undefined;
  switch (decl.kind) {
    case "def":
      return { kind: "def", value: decl.value, opaque: decl.opaque === true };
    case "axiom":
      return { kind: "axiom" };
    case "external":
      return { kind: "external" };
  }
}

/** `true` when the value is neutral (headed by a variable, const, stuck prim or projection). */
export function isNeutral(value: Value): value is NeutralValue {
  return value.tag === "Neutral";
}
