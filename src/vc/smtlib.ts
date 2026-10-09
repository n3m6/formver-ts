/**
 * SMT-LIB printing (specification 6.4).
 *
 * Three things live here:
 *
 *   - `AtomTable`: the mapping from kernel atom keys (`K.keyOfValue` strings) to SMT
 *     constants `a0`, `a1`, … and back to a representative term, which is what turns a
 *     model into a counterexample over the user's variables.
 *   - `printObligation`: the validity query — declare the atoms, assert the hypotheses as
 *     linear rows, assert the *negation* of the goal, `(check-sat)`, optionally
 *     `(get-model)`.
 *   - `printCertificateQuery`: the multiplier search of section 6.4 — solve for
 *     non-negative integer `λ` with `Σ λ_k a_k = 0` per atom and `Σ λ_k b_k < 0`.
 *
 * The encoding is over `Int` only. **`div` and `mod` are never emitted** (SMT-LIB's
 * rounding differs from JavaScript's, section 3.3): division by a constant is an opaque
 * kernel atom, and everything else is a linear form.
 */
import * as K from "../kernel/index";
import {
  formOfTerm,
  propositionTerm,
  type Atom,
  type Form,
  type Proposition,
  type Row,
} from "./linear";

/** One SMT constant: its kernel atom key, its SMT name, and a representative term. */
export interface AtomEntry {
  readonly key: string;
  readonly name: string;
  readonly representative: K.Term | undefined;
}

/**
 * Atom keys to SMT constants, in first-seen order (so a query is deterministic). The
 * representative term is quoted from the value the kernel's linear form carried; when a key
 * arrives without one (a row built from coefficients alone) the key itself is the only
 * thing a counterexample can print.
 */
export class AtomTable {
  private readonly byKey = new Map<string, AtomEntry>();
  private readonly ordered: AtomEntry[] = [];

  constructor(
    private readonly env: K.Env,
    private readonly depth: number,
  ) {}

  /** Intern `key`, optionally remembering a representative value for diagnostics. */
  intern(key: string, repr?: K.Value): AtomEntry {
    const existing = this.byKey.get(key);
    if (existing !== undefined) {
      if (existing.representative === undefined && repr !== undefined) {
        const updated: AtomEntry = { key, name: existing.name, representative: quoteSafe(this.env, this.depth, repr) };
        this.byKey.set(key, updated);
        this.ordered[this.ordered.indexOf(existing)] = updated;
        return updated;
      }
      return existing;
    }
    const entry: AtomEntry = {
      key,
      name: `a${this.ordered.length}`,
      representative: repr === undefined ? undefined : quoteSafe(this.env, this.depth, repr),
    };
    this.byKey.set(key, entry);
    this.ordered.push(entry);
    return entry;
  }

  /** Intern every atom of a form (used for rows, which carry their forms' atoms). */
  internForm(form: Form): void {
    for (const atom of form.atoms.values()) this.intern(atom.key, atom.repr);
  }

  entry(key: string): AtomEntry | undefined {
    return this.byKey.get(key);
  }

  name(key: string): string | undefined {
    return this.byKey.get(key)?.name;
  }

  entries(): readonly AtomEntry[] {
    return this.ordered;
  }

  get size(): number {
    return this.ordered.length;
  }

  /** `(declare-const a0 Int)` for every interned atom. */
  declarations(): string[] {
    return this.ordered.map((entry) => `(declare-const ${entry.name} Int)`);
  }
}

function quoteSafe(env: K.Env, depth: number, value: K.Value): K.Term | undefined {
  try {
    return K.quote(env, depth, value);
  } catch {
    return undefined;
  }
}

/** A decimal bigint, without `n` and without a leading `+`. */
const decimal = (value: bigint): string => value.toString();

/** A linear form as an SMT `Int` expression, interning any atom it mentions. */
export function printForm(atoms: AtomTable, form: Form): string {
  const terms: string[] = [];
  for (const atom of form.atoms.values()) {
    const name = atoms.intern(atom.key, atom.repr).name;
    const c = atom.coefficient;
    if (c === 1n) terms.push(name);
    else if (c === -1n) terms.push(`(- ${name})`);
    else terms.push(`(* ${decimal(c)} ${name})`);
  }
  if (terms.length === 0) return decimal(form.k);
  if (terms.length === 1 && form.k === 0n) return terms[0]!;
  const head = form.k === 0n ? "0" : decimal(form.k);
  return `(+ ${head} ${terms.join(" ")})`;
}

/** A linear `Int` term as an SMT expression, evaluating it in the obligation's context. */
export function printTerm(atoms: AtomTable, env: K.Env, depth: number, term: K.Term): string {
  return printForm(atoms, formOfTerm(env, term, depth));
}

/** `Σ aᵢ·xᵢ <= b`. */
export function printRow(atoms: AtomTable, row: Row): string {
  const terms: string[] = [];
  for (const [key, coefficient] of Object.entries(row.a)) {
    if (coefficient === 0n) continue;
    const name = atoms.name(key) ?? atoms.intern(key).name;
    if (coefficient === 1n) terms.push(name);
    else if (coefficient === -1n) terms.push(`(- ${name})`);
    else terms.push(`(* ${decimal(coefficient)} ${name})`);
  }
  const sum = terms.length === 0 ? "0" : `(+ 0 ${terms.join(" ")})`;
  return `(<= ${sum} ${decimal(row.b)})`;
}

/**
 * A proposition as an SMT-LIB Boolean, or `undefined` for a shape the linear encoding does
 * not cover (which makes the validity query *incomplete* and therefore unusable).
 */
export function printProposition(atoms: AtomTable, env: K.Env, depth: number, proposition: Proposition): string | undefined {
  switch (proposition.kind) {
    case "unit":
      return "true";
    case "empty":
      return "false";
    case "le":
      return `(<= ${printTerm(atoms, env, depth, proposition.lhs)} ${printTerm(atoms, env, depth, proposition.rhs)})`;
    case "eq": {
      if (!isIntType(proposition.type)) return undefined;
      return `(= ${printTerm(atoms, env, depth, proposition.lhs)} ${printTerm(atoms, env, depth, proposition.rhs)})`;
    }
    case "and": {
      const first = printProposition(atoms, env, depth, proposition.first);
      const second = printProposition(atoms, env, depth, proposition.second);
      if (first === undefined || second === undefined) return undefined;
      return `(and ${first} ${second})`;
    }
    case "sum": {
      const left = printProposition(atoms, env, depth, proposition.left);
      const right = printProposition(atoms, env, depth, proposition.right);
      if (left === undefined || right === undefined) return undefined;
      return `(or ${left} ${right})`;
    }
    case "not": {
      const inner = printProposition(atoms, env, depth, proposition.inner);
      return inner === undefined ? undefined : `(not ${inner})`;
    }
    case "other":
      return undefined;
  }
}

function isIntType(term: K.Term): boolean {
  return term.tag === "Prim" && term.op === K.OP_INT;
}

/** One hypothesis row with the atoms it mentions and the proof term the kernel will see. */
export interface PrintedRow {
  readonly row: Row;
  readonly atoms?: ReadonlyMap<string, Atom>;
}

export interface ObligationQuery {
  readonly env: K.Env;
  readonly depth: number;
  /** Hypotheses printed as SMT propositions: the faithful encoding. */
  readonly hypotheses?: readonly Proposition[];
  /** Hypothesis rows, for callers that only have linear rows. */
  readonly rows?: readonly PrintedRow[];
  /** `false` to ask only `(check-sat)`; `true` to also `(get-model)`. */
  readonly model?: boolean;
  /**
   * The proposition whose negation is asserted. `undefined` means "assert nothing", which
   * is what a contrariness check of the hypotheses alone needs.
   */
  readonly goal?: Proposition | undefined;
  /** Interned atoms to reuse, so several queries agree on names. */
  readonly atomTable?: AtomTable;
}

export interface ObligationScript {
  readonly script: string;
  readonly atoms: AtomTable;
  /** False when part of a hypothesis or of the goal could not be encoded. */
  readonly complete: boolean;
  /** The SMT text of the negated goal, when one was printed. */
  readonly negatedGoal?: string;
}

/** Intern the atoms of every row, then render them. */
function internRows(atoms: AtomTable, rows: readonly PrintedRow[]): void {
  for (const entry of rows) {
    if (entry.atoms !== undefined) {
      for (const atom of entry.atoms.values()) atoms.intern(atom.key, atom.repr);
    } else {
      for (const key of Object.keys(entry.row.a)) atoms.intern(key);
    }
  }
}

/**
 * The validity query: declare the atoms, assert every hypothesis (as a proposition or as a
 * row), assert the negation of the goal, and `(check-sat)`. `unsat` means valid; `sat` means
 * invalid (`model: true` adds `(get-model)`, which needs the `(check-sat)` in the same
 * script); anything else is not a verdict.
 */
export function printObligation(query: ObligationQuery): ObligationScript {
  const atoms = query.atomTable ?? new AtomTable(query.env, query.depth);
  const rows = query.rows ?? [];
  internRows(atoms, rows);
  let complete = true;
  const body: string[] = [];
  for (const entry of rows) body.push(`(assert ${printRow(atoms, entry.row)})`);
  for (const hypothesis of query.hypotheses ?? []) {
    const positive = printProposition(atoms, query.env, query.depth, hypothesis);
    if (positive === undefined) complete = false;
    else body.push(`(assert ${positive})`);
  }
  let negatedGoal: string | undefined;
  if (query.goal !== undefined && query.goal.kind !== "empty") {
    const positive = printProposition(atoms, query.env, query.depth, query.goal);
    if (positive === undefined) {
      complete = false;
    } else {
      negatedGoal = `(not ${positive})`;
      body.push(`(assert ${negatedGoal})`);
    }
  }
  const commands = [
    "(push)",
    ...atoms.declarations(),
    ...body,
    "(check-sat)",
    ...(query.model === true ? ["(get-model)"] : []),
    "(pop)",
  ];
  return { script: commands.join("\n"), atoms, complete, negatedGoal };
}

export interface CertificateQuery {
  readonly env: K.Env;
  readonly depth: number;
  /** Tightened rows: the hypotheses plus the tightened negated goal. */
  readonly rows: readonly PrintedRow[];
  readonly atomTable?: AtomTable;
}

/**
 * What the certificate script asks for: `"sat"` asks only `(check-sat)` (does a certificate
 * exist?), `"values"` also asks `(get-value (l0 …))` (which one?). Section 6.4's skeleton
 * has both commands in one script, but `(get-value …)` after an `unsat` makes Z3 print
 * `(error "model is not available")`, and *any* `(error` must be treated as a failure by
 * the binding — so the caller asks the two questions in two runs, the second only when the
 * first answered `sat` (`get-value`/`get-model` need a `(check-sat)` in the same script).
 * Both scripts re-declare the same constants and the caller passes the same `AtomTable`, so
 * the two answers are about the same query.
 */
export type CertificateMode = "sat" | "values";

export interface CertificateScript {
  readonly script: string;
  readonly atoms: AtomTable;
  /** The `l0`, `l1`, … multiplier variables, in row order. */
  readonly multipliers: readonly string[];
}

/**
 * The multiplier search of section 6.4: non-negative integer `λ` with `Σ λ_k a_k = 0` for
 * every atom and `Σ λ_k b_k < 0`. Non-negative integer multipliers suffice because any
 * rational certificate can be scaled up.
 */
export function printCertificateQuery(
  query: CertificateQuery,
  mode: CertificateMode = "sat",
): CertificateScript {
  const atoms = query.atomTable ?? new AtomTable(query.env, query.depth);
  internRows(atoms, query.rows);
  const multipliers = query.rows.map((_, index) => `l${index}`);
  const literals = query.rows.map((entry, index) => `(* ${decimal(entry.row.b)} l${index})`);
  const lines: string[] = ["(push)"];
  for (const name of multipliers) lines.push(`(declare-const ${name} Int)`, `(assert (>= ${name} 0))`);
  for (const atom of atoms.entries()) {
    const terms = query.rows.map(
      (entry, index) => `(* ${decimal(entry.row.a[atom.key] ?? 0n)} l${index})`,
    );
    lines.push(`(assert (= (+ 0 ${terms.join(" ")}) 0))`);
  }
  lines.push(`(assert (< (+ 0 ${literals.join(" ")}) 0))`);
  lines.push(`(check-sat)`);
  if (mode === "values" && multipliers.length > 0) lines.push(`(get-value (${multipliers.join(" ")}))`);
  lines.push("(pop)");
  return { script: lines.join("\n"), atoms, multipliers };
}

/**
 * The first line of an output that is exactly a verdict. `check-sat` answers before any
 * model or value the script goes on to print, so scanning from the top is what identifies
 * the verdict rather than a line of a model.
 */
export function parseVerdict(output: string): "sat" | "unsat" | "unknown" | undefined {
  for (const line of output.split("\n")) {
    const text = line.trim();
    if (text === "sat" || text === "unsat" || text === "unknown") return text;
  }
  return undefined;
}

/** Read one balanced S-expression starting at `start`, skipping leading whitespace. */
function readSexpr(text: string, start: number): { readonly text: string; readonly end: number } {
  let index = start;
  while (index < text.length && /\s/.test(text[index]!)) index += 1;
  if (text[index] !== "(") {
    let end = index;
    while (end < text.length && !/[\s)]/.test(text[end]!)) end += 1;
    return { text: text.slice(index, end), end };
  }
  let depth = 0;
  let end = index;
  for (; end < text.length; end += 1) {
    if (text[end] === "(") depth += 1;
    else if (text[end] === ")") {
      depth -= 1;
      if (depth === 0) {
        end += 1;
        break;
      }
    }
  }
  return { text: text.slice(index, end), end };
}

/** Parse a numeral, including Z3's `(- 3)` form, into a decimal string. */
function decodeNumeral(text: string): string | undefined {
  const trimmed = text.trim();
  if (/^-?\d+$/.test(trimmed)) return BigInt(trimmed).toString();
  const negative = /^\(-\s+(\d+)\)$/.exec(trimmed);
  if (negative !== null) return (-BigInt(negative[1]!)).toString();
  return undefined;
}

/**
 * Decode `(get-model)` output into `SMT name -> value` pairs. Z3 prints one
 * `(define-fun NAME () Int VALUE)` per constant; values are numerals or `(- N)`. A value
 * in any other shape (an uninterpreted term) is kept as its raw text so the caller can
 * still see it. Function definitions (`(define-fun f ((x Int)) …)`) are skipped.
 */
export function decodeModel(output: string): Record<string, string> {
  const out: Record<string, string> = {};
  const pattern = /\(define-fun\s+([^\s()]+)\s*\(\s*\)\s*[^\s()]+\s*/g;
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(output)) !== null) {
    const name = match[1]!;
    const value = readSexpr(output, pattern.lastIndex);
    const raw = value.text.trim();
    out[name] = decodeNumeral(raw) ?? raw;
    pattern.lastIndex = value.end;
  }
  return out;
}

/** Decode a `(get-value (l0 l1 …))` response into `name -> decimal value` pairs. */
export function decodeValues(
  output: string,
  names: readonly string[],
): Record<string, string> | undefined {
  const values: Record<string, string> = {};
  for (const name of names) {
    const pattern = new RegExp(`\\(${name}\\s+(-?\\d+)\\)`);
    const match = pattern.exec(output);
    if (match === null) return undefined;
    values[name] = BigInt(match[1]!).toString();
  }
  return values;
}
