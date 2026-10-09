/**
 * Bidirectional type checking: `infer` synthesizes a type, `check` verifies a term
 * against an expected type and falls back to infer-then-convert.
 *
 * Sorts (specification section 6.1.2):
 *
 *   Type l : Type (l + 1)          there is no Type : Type
 *   Pi/Sigma: A : Type i, B : Type j  =>  Pi A B : Type (max i j)
 *
 * Propositions live in `Type 0`; there is no separate `Prop`.
 *
 * A typing context is a pair of parallel lists indexed by de Bruijn *level*: the type and
 * the value of each variable. For an ordinary binder the value is the variable itself;
 * for a `Let` binding it is the bound value, which is how zeta is realized during
 * checking. Conversion is always called with `depth = ctx.values.length`, so the fresh
 * variables that `conv.ts` invents cannot collide with the context.
 */
import { lookupPrim, OP_EMPTY, OP_INT } from "./builtins";
import { convValue } from "./conv";
import type { Env } from "./env";
import { err, internalError, kernelError, ok, type KernelError, type Result } from "./errors";
import { applyClosure, evalTerm, fstOf } from "./eval";
import { checkFarkas } from "./farkas";
import { quote } from "./quote";
import { formatTerm, type Level, type PrimOp, type Term } from "./term";
import type { Closure, Value } from "./value";
import { vpi, vprim, vsort, vvar } from "./value";

export interface Ctx {
  readonly env: Env;
  /** `types[level]` is the type of the variable at that level. */
  readonly types: readonly Value[];
  /** `values[level]` is the value of that variable (itself, or a `Let` value). */
  readonly values: readonly Value[];
}

export function emptyCtx(env: Env): Ctx {
  return { env, types: [], values: [] };
}

function bindVar(ctx: Ctx, type: Value): Ctx {
  return {
    env: ctx.env,
    types: [...ctx.types, type],
    values: [...ctx.values, vvar(ctx.values.length)],
  };
}

function defineVar(ctx: Ctx, type: Value, value: Value): Ctx {
  return { env: ctx.env, types: [...ctx.types, type], values: [...ctx.values, value] };
}

function typeOfVar(ctx: Ctx, index: number): Value | undefined {
  const slot = ctx.values.length - 1 - index;
  if (slot < 0 || slot >= ctx.types.length) return undefined;
  return ctx.types[slot];
}

/** Renders a value as a type for diagnostics; never fails. */
function render(ctx: Ctx, value: Value): string {
  try {
    return formatTerm(quote(ctx.env, ctx.values.length, value));
  } catch {
    return "<unprintable>";
  }
}

// ---------------------------------------------------------------------------
// Inference
// ---------------------------------------------------------------------------

export function infer(ctx: Ctx, term: Term): Result<Value, KernelError> {
  const env = ctx.env;
  switch (term.tag) {
    case "Var": {
      const type = typeOfVar(ctx, term.index);
      if (type === undefined) {
        return err(kernelError("unbound-variable", `unbound variable index ${term.index}`, { term }));
      }
      return ok(type);
    }

    case "Sort":
      // Type l : Type (l + 1). There is no Type : Type.
      return ok(vsort(term.level + 1));

    case "Pi":
      return inferPiLike(ctx, term.domain, term.body);

    case "Sigma":
      return inferPiLike(ctx, term.first, term.second);

    case "Lam": {
      const domainLevel = inferLevel(ctx, term.domain);
      if (!domainLevel.ok) return domainLevel;
      const domainValue = evalTerm(env, term.domain, ctx.values);
      const inner = bindVar(ctx, domainValue);
      const bodyType = infer(inner, term.body);
      if (!bodyType.ok) return bodyType;
      const codomain: Closure = {
        name: term.name,
        body: quote(env, inner.values.length, bodyType.value),
        env: ctx.values,
      };
      return ok(vpi(term.name, domainValue, codomain));
    }

    case "App": {
      const fnType = infer(ctx, term.fn);
      if (!fnType.ok) return fnType;
      if (fnType.value.tag !== "Pi") {
        return err(
          kernelError(
            "not-a-function",
            `${formatTerm(term.fn)} has type ${render(ctx, fnType.value)}, which is not a function type`,
            { term },
          ),
        );
      }
      const argCheck = check(ctx, term.arg, fnType.value.domain);
      if (!argCheck.ok) return argCheck;
      return ok(applyClosure(env, fnType.value.codomain, evalTerm(env, term.arg, ctx.values)));
    }

    case "Pair": {
      const sigmaLevel = inferLevel(ctx, term.sigma);
      if (!sigmaLevel.ok) return sigmaLevel;
      const sigmaValue = evalTerm(env, term.sigma, ctx.values);
      if (sigmaValue.tag !== "Sigma") {
        return err(
          kernelError("not-a-sigma", `the annotation of a pair must be a Sigma type, but ${formatTerm(term.sigma)} is ${render(ctx, sigmaValue)}`, {
            term,
          }),
        );
      }
      const firstCheck = check(ctx, term.first, sigmaValue.first);
      if (!firstCheck.ok) return firstCheck;
      const firstValue = evalTerm(env, term.first, ctx.values);
      const secondCheck = check(ctx, term.second, applyClosure(env, sigmaValue.second, firstValue));
      if (!secondCheck.ok) return secondCheck;
      return ok(sigmaValue);
    }

    case "Fst": {
      const pairType = infer(ctx, term.pair);
      if (!pairType.ok) return pairType;
      if (pairType.value.tag !== "Sigma") {
        return err(
          kernelError("not-a-sigma", `fst expects a pair, but ${formatTerm(term.pair)} has type ${render(ctx, pairType.value)}`, {
            term,
          }),
        );
      }
      return ok(pairType.value.first);
    }

    case "Snd": {
      const pairType = infer(ctx, term.pair);
      if (!pairType.ok) return pairType;
      if (pairType.value.tag !== "Sigma") {
        return err(
          kernelError("not-a-sigma", `snd expects a pair, but ${formatTerm(term.pair)} has type ${render(ctx, pairType.value)}`, {
            term,
          }),
        );
      }
      const pairValue = evalTerm(env, term.pair, ctx.values);
      return ok(applyClosure(env, pairType.value.second, fstOf(pairValue)));
    }

    case "Let": {
      const typeLevel = inferLevel(ctx, term.type);
      if (!typeLevel.ok) return typeLevel;
      const typeValue = evalTerm(env, term.type, ctx.values);
      const valueCheck = check(ctx, term.value, typeValue);
      if (!valueCheck.ok) return valueCheck;
      const value = evalTerm(env, term.value, ctx.values);
      return infer(defineVar(ctx, typeValue, value), term.body);
    }

    case "Const": {
      const decl = env.decls.get(term.name);
      if (decl === undefined) {
        return err(kernelError("unbound-constant", `unknown global name ${term.name}`, { term }));
      }
      return ok(evalTerm(env, decl.type, []));
    }

    case "IntLit":
      return ok(vprim(OP_INT, 0, []));

    case "Prim":
      return inferPrim(ctx, term.op, term.level ?? 0, term.args, term);

    case "Farkas":
      return inferFarkas(ctx, term.hyps, term.coeffs, term);
  }
}

function inferPiLike(ctx: Ctx, domain: Term, body: Term): Result<Value, KernelError> {
  const domainLevel = inferLevel(ctx, domain);
  if (!domainLevel.ok) return domainLevel;
  const inner = bindVar(ctx, evalTerm(ctx.env, domain, ctx.values));
  const bodyLevel = inferLevel(inner, body);
  if (!bodyLevel.ok) return bodyLevel;
  return ok(vsort(Math.max(domainLevel.value, bodyLevel.value)));
}

/** Infers a term's type and requires it to be a sort, returning its level. */
function inferLevel(ctx: Ctx, term: Term): Result<Level, KernelError> {
  const inferred = infer(ctx, term);
  if (!inferred.ok) return inferred;
  if (inferred.value.tag !== "Sort") {
    return err(
      kernelError("not-a-type", `${formatTerm(term)} is not a type`, {
        term,
        actual: quote(ctx.env, ctx.values.length, inferred.value),
      }),
    );
  }
  return ok(inferred.value.level);
}

function inferPrim(
  ctx: Ctx,
  op: PrimOp,
  level: Level,
  args: readonly Term[],
  whole: Term,
): Result<Value, KernelError> {
  const info = lookupPrim(op);
  if (info === undefined) {
    return err(kernelError("unknown-prim", `unknown built-in op ${op}`, { term: whole, op }));
  }
  if (args.length !== info.arity) {
    return err(
      kernelError("prim-arity", `${op} takes ${info.arity} arguments, but got ${args.length}`, { term: whole, op }),
    );
  }
  // The op's type is a closed Pi telescope; walk it, checking each argument in turn.
  let type = evalTerm(ctx.env, info.typeFor(level), []);
  for (let index = 0; index < args.length; index += 1) {
    const arg = args[index]!;
    if (type.tag !== "Pi") {
      return err(kernelError("internal", `the type of built-in ${op} is not a Pi telescope`, { op }));
    }
    const argCheck = check(ctx, arg, type.domain);
    if (!argCheck.ok) return argCheck;
    if (info.positiveLiteralArgs?.includes(index) === true && (arg.tag !== "IntLit" || arg.value <= 0n)) {
      return err(
        kernelError(
          "prim-not-literal",
          `${op} requires argument ${index + 1} to be a positive integer literal (only then is its built-in lemma sound), but got ${formatTerm(arg)}`,
          { term: whole, op },
        ),
      );
    }
    type = applyClosure(ctx.env, type.codomain, evalTerm(ctx.env, arg, ctx.values));
  }
  return ok(type);
}

/**
 * `Farkas { hyps, coeffs } : Empty` when `farkas.ts` accepts the certificate for the
 * *types* of the hypotheses. Each hypothesis is checked as a term first; its inferred type
 * is handed over as a value, so rows come from linear normal forms rather than syntax.
 */
function inferFarkas(
  ctx: Ctx,
  hyps: readonly Term[],
  coeffs: readonly bigint[],
  whole: Term,
): Result<Value, KernelError> {
  const hypTypes: Value[] = [];
  for (const hyp of hyps) {
    const inferred = infer(ctx, hyp);
    if (!inferred.ok) return inferred;
    hypTypes.push(inferred.value);
  }
  const verdict = checkFarkas({ hypTypes, coeffs });
  if (!verdict.ok) return err({ ...verdict.error, term: whole });
  return ok(vprim(OP_EMPTY, 0, []));
}

// ---------------------------------------------------------------------------
// Checking
// ---------------------------------------------------------------------------

export function check(ctx: Ctx, term: Term, expected: Value): Result<void, KernelError> {
  const env = ctx.env;
  switch (term.tag) {
    case "Lam": {
      if (expected.tag !== "Pi") return checkByInference(ctx, term, expected);
      const domainLevel = inferLevel(ctx, term.domain);
      if (!domainLevel.ok) return domainLevel;
      const domainValue = evalTerm(env, term.domain, ctx.values);
      if (!convValue(env, ctx.values.length, domainValue, expected.domain)) {
        return err(
          kernelError(
            "type-mismatch",
            `the lambda's domain ${render(ctx, domainValue)} does not match the expected domain ${render(ctx, expected.domain)}`,
            { term },
          ),
        );
      }
      const level = ctx.values.length;
      const inner = bindVar(ctx, expected.domain);
      return check(inner, term.body, applyClosure(env, expected.codomain, vvar(level)));
    }

    case "Pair": {
      if (expected.tag !== "Sigma") return checkByInference(ctx, term, expected);
      const sigmaLevel = inferLevel(ctx, term.sigma);
      if (!sigmaLevel.ok) return sigmaLevel;
      const sigmaValue = evalTerm(env, term.sigma, ctx.values);
      if (sigmaValue.tag !== "Sigma" || !convValue(env, ctx.values.length, sigmaValue, expected)) {
        return err(
          kernelError(
            "type-mismatch",
            `the pair's annotation ${render(ctx, sigmaValue)} does not match the expected Sigma type ${render(ctx, expected)}`,
            { term },
          ),
        );
      }
      const firstCheck = check(ctx, term.first, expected.first);
      if (!firstCheck.ok) return firstCheck;
      const firstValue = evalTerm(env, term.first, ctx.values);
      return check(ctx, term.second, applyClosure(env, expected.second, firstValue));
    }

    case "Let": {
      const typeLevel = inferLevel(ctx, term.type);
      if (!typeLevel.ok) return typeLevel;
      const typeValue = evalTerm(env, term.type, ctx.values);
      const valueCheck = check(ctx, term.value, typeValue);
      if (!valueCheck.ok) return valueCheck;
      const value = evalTerm(env, term.value, ctx.values);
      return check(defineVar(ctx, typeValue, value), term.body, expected);
    }

    default:
      return checkByInference(ctx, term, expected);
  }
}

function checkByInference(ctx: Ctx, term: Term, expected: Value): Result<void, KernelError> {
  const inferred = infer(ctx, term);
  if (!inferred.ok) return inferred;
  if (!convValue(ctx.env, ctx.values.length, inferred.value, expected)) {
    return err(
      kernelError("type-mismatch", `expected ${render(ctx, expected)} but got ${render(ctx, inferred.value)}`, {
        term,
        expected: quote(ctx.env, ctx.values.length, expected),
        actual: quote(ctx.env, ctx.values.length, inferred.value),
      }),
    );
  }
  return ok(undefined);
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

function guard<T>(thunk: () => Result<T, KernelError>): Result<T, KernelError> {
  try {
    return thunk();
  } catch (cause) {
    return err(internalError(cause));
  }
}

/** Infers the type of a closed term; the returned type is in normal form. */
export function inferType(env: Env, term: Term): Result<Term, KernelError> {
  return guard(() => {
    const inferred = infer(emptyCtx(env), term);
    if (!inferred.ok) return inferred;
    return ok(quote(env, 0, inferred.value));
  });
}

/** Checks a closed term against a closed type, which must itself be a well-formed type. */
export function checkType(env: Env, term: Term, type: Term): Result<void, KernelError> {
  return guard(() => {
    const ctx = emptyCtx(env);
    const level = inferLevel(ctx, type);
    if (!level.ok) return level;
    return check(ctx, term, evalTerm(env, type, []));
  });
}

/** Checks that a term is a well-formed type and returns its universe level. */
export function isTypeTerm(env: Env, term: Term): Result<Level, KernelError> {
  return guard(() => inferLevel(emptyCtx(env), term));
}
