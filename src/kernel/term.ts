/**
 * Kernel term syntax (specification section 6.1.1).
 *
 * Binding is by de Bruijn index: `Var 0` is the innermost binder. The `name` fields on
 * `Pi`, `Lam`, `Sigma` and `Let` are for printing and diagnostics only; they carry no
 * meaning for binding.
 *
 * This is the bottom of the kernel: it imports nothing, from inside or outside
 * `src/kernel/`.
 */

/** Concrete universe levels. There is no level polymorphism in the MVP. */
export type Level = number;

/**
 * Tag of a primitive op, for example `"Le"` or `"get"`. The registry that gives each op
 * its type, reduction rule and conversion rule is `PRIMS` in `builtins.ts`.
 */
export type PrimOp = string;

export type Term =
  | { tag: "Var"; index: number } // de Bruijn index
  | { tag: "Sort"; level: Level } // Type level
  | { tag: "Pi"; name: string; domain: Term; body: Term }
  | { tag: "Lam"; name: string; domain: Term; body: Term } // annotated, keeps inference simple
  | { tag: "App"; fn: Term; arg: Term }
  | { tag: "Sigma"; name: string; first: Term; second: Term }
  | { tag: "Pair"; sigma: Term; first: Term; second: Term } // annotated with its Sigma type
  | { tag: "Fst"; pair: Term }
  | { tag: "Snd"; pair: Term }
  | { tag: "Let"; name: string; type: Term; value: Term; body: Term }
  | { tag: "Const"; name: string } // global declaration
  | { tag: "IntLit"; value: bigint }
  | { tag: "Prim"; op: PrimOp; level?: Level; args: Term[] } // fully applied built-ins
  | { tag: "Farkas"; hyps: Term[]; coeffs: bigint[] }; // : Empty, when the certificate checks

// ---------------------------------------------------------------------------
// Constructors
// ---------------------------------------------------------------------------

export const varTerm = (index: number): Term => ({ tag: "Var", index });

export const sort = (level: Level): Term => ({ tag: "Sort", level });

export function pi(name: string, domain: Term, body: Term): Term {
  return { tag: "Pi", name, domain, body };
}

export function lam(name: string, domain: Term, body: Term): Term {
  return { tag: "Lam", name, domain, body };
}

export function app(fn: Term, arg: Term): Term {
  return { tag: "App", fn, arg };
}

export function appMany(fn: Term, args: readonly Term[]): Term {
  let out = fn;
  for (const arg of args) out = app(out, arg);
  return out;
}

export function sigma(name: string, first: Term, second: Term): Term {
  return { tag: "Sigma", name, first, second };
}

export function pair(sigmaType: Term, first: Term, second: Term): Term {
  return { tag: "Pair", sigma: sigmaType, first, second };
}

export const fst = (pairTerm: Term): Term => ({ tag: "Fst", pair: pairTerm });

export const snd = (pairTerm: Term): Term => ({ tag: "Snd", pair: pairTerm });

export function letTerm(name: string, type: Term, value: Term, body: Term): Term {
  return { tag: "Let", name, type, value, body };
}

/** `let_` is an alias for `letTerm` (`let` is a reserved word). */
export const let_ = letTerm;

export const constTerm = (name: string): Term => ({ tag: "Const", name });

export const intLit = (value: bigint | number): Term => ({
  tag: "IntLit",
  value: typeof value === "bigint" ? value : BigInt(value),
});

export const primTerm = (op: PrimOp, args: readonly Term[], level?: Level): Term =>
  level === undefined ? { tag: "Prim", op, args: [...args] } : { tag: "Prim", op, level, args: [...args] };

export const farkasTerm = (hyps: readonly Term[], coeffs: readonly bigint[]): Term => ({
  tag: "Farkas",
  hyps: [...hyps],
  coeffs: [...coeffs],
});

// ---------------------------------------------------------------------------
// Erasure
// ---------------------------------------------------------------------------

/**
 * A term with proofs, types and universe annotations removed, kept for the differential
 * interpreter (milestone 9). Binders that remain (`Lam`, `Let`) still bind exactly one
 * variable, so de Bruijn indices are unchanged; everything erased sits in a position the
 * interpreter never inspects for computation.
 */
export type ErasedTerm =
  | { tag: "Var"; index: number }
  | { tag: "Lam"; name: string; body: ErasedTerm }
  | { tag: "App"; fn: ErasedTerm; arg: ErasedTerm }
  | { tag: "Pair"; first: ErasedTerm; second: ErasedTerm }
  | { tag: "Fst"; pair: ErasedTerm }
  | { tag: "Snd"; pair: ErasedTerm }
  | { tag: "Let"; name: string; value: ErasedTerm; body: ErasedTerm }
  | { tag: "Const"; name: string }
  | { tag: "IntLit"; value: bigint }
  | { tag: "Prim"; op: PrimOp; args: ErasedTerm[] }
  | { tag: "Erased" };

export function erase(term: Term): ErasedTerm {
  switch (term.tag) {
    case "Var":
      return { tag: "Var", index: term.index };
    case "Lam":
      return { tag: "Lam", name: term.name, body: erase(term.body) };
    case "App":
      return { tag: "App", fn: erase(term.fn), arg: erase(term.arg) };
    case "Pair":
      return { tag: "Pair", first: erase(term.first), second: erase(term.second) };
    case "Fst":
      return { tag: "Fst", pair: erase(term.pair) };
    case "Snd":
      return { tag: "Snd", pair: erase(term.pair) };
    case "Let":
      return { tag: "Let", name: term.name, value: erase(term.value), body: erase(term.body) };
    case "Const":
      return { tag: "Const", name: term.name };
    case "IntLit":
      return { tag: "IntLit", value: term.value };
    case "Prim":
      return { tag: "Prim", op: term.op, args: term.args.map(erase) };
    // Types, proofs and the certificate itself have no runtime content.
    case "Sort":
    case "Pi":
    case "Sigma":
    case "Farkas":
      return { tag: "Erased" };
  }
}

// ---------------------------------------------------------------------------
// Printing
// ---------------------------------------------------------------------------

const isAtomic = (term: Term): boolean =>
  term.tag === "Var" ||
  term.tag === "Const" ||
  term.tag === "IntLit" ||
  (term.tag === "Prim" && term.args.length === 0);

function wrap(term: Term, names: readonly string[]): string {
  const text = print(term, names);
  return isAtomic(term) ? text : `(${text})`;
}

function print(term: Term, names: readonly string[]): string {
  switch (term.tag) {
    case "Var": {
      // `names` is ordered innermost-first, so the de Bruijn index is the array index.
      const name = names[term.index];
      return name === undefined ? `?${term.index}` : name;
    }
    case "Sort":
      return `Type ${term.level}`;
    case "Pi": {
      const domain = print(term.domain, names);
      const body = print(term.body, [term.name, ...names]);
      return term.name === "_" ? `(${domain} -> ${body})` : `((${term.name} : ${domain}) -> ${body})`;
    }
    case "Lam": {
      const domain = print(term.domain, names);
      const body = print(term.body, [term.name, ...names]);
      return `(fun (${term.name} : ${domain}) => ${body})`;
    }
    case "App":
      return `${wrap(term.fn, names)} ${wrap(term.arg, names)}`;
    case "Sigma": {
      const first = print(term.first, names);
      const second = print(term.second, [term.name, ...names]);
      return `(Sig (${term.name} : ${first}). ${second})`;
    }
    case "Pair":
      return `<${print(term.first, names)}, ${print(term.second, names)}>`;
    case "Fst":
      return `fst ${wrap(term.pair, names)}`;
    case "Snd":
      return `snd ${wrap(term.pair, names)}`;
    case "Let":
      return `(let ${term.name} : ${print(term.type, names)} = ${print(term.value, names)} in ${print(term.body, [
        term.name,
        ...names,
      ])})`;
    case "Const":
      return term.name;
    case "IntLit":
      return term.value.toString();
    case "Prim":
      return `${term.op}(${term.args.map((arg) => print(arg, names)).join(", ")})`;
    case "Farkas":
      return `farkas[${term.hyps.map((h) => print(h, names)).join(", ")}; ${term.coeffs
        .map((c) => c.toString())
        .join(", ")}]`;
  }
}

/** Renders a term for diagnostics and the CLI. Not a parser round-trip. */
export function formatTerm(term: Term): string {
  return print(term, []);
}

// ---------------------------------------------------------------------------
// de Bruijn-safe term builder
// ---------------------------------------------------------------------------

/**
 * A named scope used to build terms without doing index arithmetic by hand. Names are
 * stored innermost-first; `index` returns the de Bruijn index of the innermost binder
 * with that name, so shadowing behaves as expected.
 */
export class Scope {
  private readonly names: readonly string[];

  private constructor(names: readonly string[]) {
    this.names = names;
  }

  static readonly empty: Scope = new Scope([]);

  bind(name: string): Scope {
    return new Scope([name, ...this.names]);
  }

  index(name: string): number {
    const index = this.names.indexOf(name);
    if (index < 0) throw new Error(`kernel term builder: unbound variable ${name}`);
    return index;
  }
}

/** A term under construction; applied to the scope that is in effect for it. */
export type Mk = (scope: Scope) => Term;

export function mk(term: Mk): Term {
  return term(Scope.empty);
}

export const varMk =
  (name: string): Mk =>
  (scope) =>
    varTerm(scope.index(name));

export const sortMk =
  (level: Level): Mk =>
  () =>
    sort(level);

export const constMk =
  (name: string): Mk =>
  () =>
    constTerm(name);

export const intLitMk =
  (value: bigint | number): Mk =>
  () =>
    intLit(value);

export const appMk =
  (fn: Mk, arg: Mk): Mk =>
  (scope) =>
    app(fn(scope), arg(scope));

export const appManyMk =
  (fn: Mk, args: readonly Mk[]): Mk =>
  (scope) => {
    let out = fn(scope);
    for (const arg of args) out = app(out, arg(scope));
    return out;
  };

export const primMk =
  (op: PrimOp, args: readonly Mk[], level?: Level): Mk =>
  (scope) =>
    primTerm(
      op,
      args.map((arg) => arg(scope)),
      level,
    );

export const piMk =
  (name: string, domain: Mk, body: Mk): Mk =>
  (scope) =>
    pi(name, domain(scope), body(scope.bind(name)));

export const lamMk =
  (name: string, domain: Mk, body: Mk): Mk =>
  (scope) =>
    lam(name, domain(scope), body(scope.bind(name)));

export const sigmaMk =
  (name: string, first: Mk, second: Mk): Mk =>
  (scope) =>
    sigma(name, first(scope), second(scope.bind(name)));

export const letMk =
  (name: string, type: Mk, value: Mk, body: Mk): Mk =>
  (scope) =>
    letTerm(name, type(scope), value(scope), body(scope.bind(name)));

export const pairMk =
  (sigmaType: Mk, first: Mk, second: Mk): Mk =>
  (scope) =>
    pair(sigmaType(scope), first(scope), second(scope));

export const farkasMk =
  (hyps: readonly Mk[], coeffs: readonly bigint[]): Mk =>
  (scope) =>
    farkasTerm(
      hyps.map((hyp) => hyp(scope)),
      coeffs,
    );

export const fstMk =
  (pairTerm: Mk): Mk =>
  (scope) =>
    fst(pairTerm(scope));

export const sndMk =
  (pairTerm: Mk): Mk =>
  (scope) =>
    snd(pairTerm(scope));
