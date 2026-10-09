/**
 * The Farkas rule (specification section 6.1.4): `Farkas { hyps, coeffs } : Empty`.
 *
 * Milestone 2 implements the *arithmetic* completely — row tightening by the GCD of the
 * coefficients, and the certificate check `Σ λᵢ aᵢ = 0` per atom with `Σ λᵢ bᵢ < 0` — and
 * extracts rows for hypotheses whose type is `Le a b` between integer *literals*, which
 * is enough for `Farkas` to be typeable as `Empty` end to end.
 *
 * Milestone 3 replaces `rowOfLe` with extraction from the linear normal form of `t - s`
 * (values of type `Int` built from literals, `add`, `sub`, `neg`, `mulConst`), keyed by
 * canonical atom keys with irrelevant proof arguments erased. Nothing else in this file
 * changes: `tightenRow` and `checkCertificate` are already final, and `src/vc/linear.ts`
 * must duplicate them exactly so that the multipliers it finds are accepted here.
 */
import { OP_LE } from "./builtins";
import { err, kernelError, ok, type KernelError, type Result } from "./errors";
import { formatTerm, type Term } from "./term";

/** A linear row `Σ aᵢ · xᵢ <= b` over integer-valued atoms, after tightening. */
export interface Row {
  readonly a: Readonly<Record<string, bigint>>;
  readonly b: bigint;
}

/** Non-negative greatest common divisor; `gcd(0, 0) = 0`. */
export function gcd(a: bigint, b: bigint): bigint {
  let x = a < 0n ? -a : a;
  let y = b < 0n ? -b : b;
  while (y !== 0n) {
    const next = x % y;
    x = y;
    y = next;
  }
  return x;
}

/** Floor division for a positive divisor (`bigint` division truncates toward zero). */
export function floorDiv(a: bigint, b: bigint): bigint {
  const quotient = a / b;
  const remainder = a % b;
  return remainder !== 0n && remainder < 0n ? quotient - 1n : quotient;
}

/**
 * Integer tightening: divide every coefficient by the GCD of the non-zero coefficients
 * and floor the bound. Sound because atoms are integer-valued. Rows with no non-zero
 * coefficient (or with GCD 1) are returned with their zero coefficients dropped.
 */
export function tightenRow(row: Row): Row {
  const coefficients = new Map<string, bigint>();
  for (const [atom, coefficient] of Object.entries(row.a)) {
    if (coefficient !== 0n) coefficients.set(atom, coefficient);
  }
  let divisor = 0n;
  for (const coefficient of coefficients.values()) divisor = gcd(divisor, coefficient);
  if (divisor <= 1n) return { a: Object.fromEntries(coefficients), b: row.b };
  const tightened = new Map<string, bigint>();
  for (const [atom, coefficient] of coefficients) tightened.set(atom, coefficient / divisor);
  return { a: Object.fromEntries(tightened), b: floorDiv(row.b, divisor) };
}

/**
 * `rows` must already be tightened. Accepts when the multipliers are non-negative, cancel
 * every atom, and leave a negative bound.
 */
export function checkCertificate(rows: readonly Row[], coefficients: readonly bigint[]): boolean {
  if (coefficients.length !== rows.length) return false;
  const total = new Map<string, bigint>();
  let bound = 0n;
  for (let i = 0; i < rows.length; i += 1) {
    const multiplier = coefficients[i]!;
    if (multiplier < 0n) return false;
    const row = rows[i]!;
    for (const [atom, coefficient] of Object.entries(row.a)) {
      total.set(atom, (total.get(atom) ?? 0n) + multiplier * coefficient);
    }
    bound += multiplier * row.b;
  }
  for (const coefficient of total.values()) {
    if (coefficient !== 0n) return false;
  }
  return bound < 0n;
}

/** The kernel's view of one certificate: hypothesis types, and one coefficient each. */
export interface FarkasRule {
  readonly hypTypes: readonly Term[];
  readonly coeffs: readonly bigint[];
}

/**
 * The type-level rule: accepts exactly when the certificate refutes the hypotheses.
 * Called by `check.ts` when it types a `Farkas` term.
 */
export function checkFarkas(rule: FarkasRule): Result<void, KernelError> {
  const { hypTypes, coeffs } = rule;
  if (hypTypes.length !== coeffs.length) {
    return err(
      kernelError(
        "farkas-shape",
        `a Farkas certificate needs one coefficient per hypothesis, but got ${coeffs.length} coefficients for ${hypTypes.length} hypotheses`,
      ),
    );
  }
  for (const coefficient of coeffs) {
    if (coefficient < 0n) {
      return err(kernelError("farkas-negative-coefficient", "Farkas multipliers must be non-negative"));
    }
  }
  const rows = rowsOf(hypTypes);
  if (!rows.ok) return rows;
  if (!checkCertificate(rows.value.map(tightenRow), coeffs)) {
    return err(
      kernelError("farkas-invalid", "the Farkas certificate does not derive a contradiction from the tightened rows"),
    );
  }
  return ok(undefined);
}

/** One row per hypothesis type, which must be `Le s t` (`Lt` unfolds to `Le` in eval). */
function rowsOf(hypTypes: readonly Term[]): Result<Row[], KernelError> {
  const rows: Row[] = [];
  for (const type of hypTypes) {
    const row = rowOfLe(type);
    if (!row.ok) return row;
    rows.push(row.value);
  }
  return ok(rows);
}

/**
 * `Le s t` means `s <= t`, that is `s - t <= 0`, that is `0 <= t - s`: the row has the
 * coefficients of the atoms of `s - t` and bound `t - s`.
 *
 * Milestone 2: only literal bounds, so the row has no atoms. Milestone 3 generalizes this
 * to the linear normal form of `s - t` over atom keys.
 */
function rowOfLe(type: Term): Result<Row, KernelError> {
  if (type.tag !== "Prim" || type.op !== OP_LE || type.args.length !== 2) {
    return err(
      kernelError(
        "farkas-not-a-le-hypothesis",
        `a Farkas hypothesis must have type Le s t, but this one has type ${formatTerm(type)}`,
        { term: type, op: type.tag === "Prim" ? type.op : undefined },
      ),
    );
  }
  const lhs = type.args[0];
  const rhs = type.args[1];
  if (lhs === undefined || rhs === undefined || lhs.tag !== "IntLit" || rhs.tag !== "IntLit") {
    return err(
      kernelError(
        "farkas-unimplemented",
        "milestone 2 checks only certificates whose hypotheses are Le between integer literals; linear normal forms over atoms arrive in milestone 3",
        { term: type },
      ),
    );
  }
  return ok({ a: {}, b: rhs.value - lhs.value });
}
