/**
 * The Farkas rule (specification section 6.1.4): `Farkas { hyps, coeffs } : Empty`.
 *
 * A hypothesis whose type is `Le s t` becomes the row `c · atoms <= b`, where the linear
 * form of `s - t` is `Σ cᵢ xᵢ + k` and `b = -k` (so `s <= t` reads as `s - t <= 0`).
 * Every row is tightened by the GCD of its non-zero coefficients, and the certificate is
 * accepted when the multipliers are non-negative, cancel every atom, and leave a negative
 * bound. All arithmetic is `bigint`.
 *
 * `tightenRow` and `checkCertificate` are the arithmetic that the untrusted
 * `src/vc/linear.ts` deliberately duplicates in milestone 6, so their signatures and
 * semantics are frozen. `gcd`/`floorDiv` live in `linear.ts` (the trusted module that
 * needs them for `divFloor`/`divTrunc`) and are re-exported here.
 */
import { OP_LE, irrelevantOf } from "./builtins";
import { err, kernelError, ok, type KernelError, type Result } from "./errors";
import { floorDiv, formOf, formSub, gcd, keyOfValue } from "./linear";
import { constructorHead, type Value } from "./value";

export { floorDiv, gcd };

/** A linear row `Σ aᵢ · xᵢ <= b` over integer-valued atoms, after tightening. */
export interface Row {
  readonly a: Readonly<Record<string, bigint>>;
  readonly b: bigint;
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

/**
 * The kernel's view of one certificate: the hypotheses' *inferred types* as values, in
 * order, and one multiplier each. `check.ts` passes the values it already inferred, so
 * rows are built from semantic values rather than by re-parsing terms.
 */
export interface FarkasRule {
  readonly hypTypes: readonly Value[];
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

/** One row per hypothesis type, whose weak head normal form must be `Le s t`. */
function rowsOf(hypTypes: readonly Value[]): Result<Row[], KernelError> {
  const rows: Row[] = [];
  for (const type of hypTypes) {
    const row = rowOfLe(type);
    if (!row.ok) return row;
    rows.push(row.value);
  }
  return ok(rows);
}

/**
 * The row of a hypothesis whose type is `Le s t`: `s - t <= 0`, so it takes the
 * coefficients of the linear form of `s - t` and the bound `-k`, where `k` is that form's
 * constant. `Lt a b` is the definition `Le (a + 1) b`, so it is already `Le` by the time a
 * value reaches here. Exported for the tests and for milestone 6's comparison against
 * `src/vc/linear.ts`.
 */
export function rowOfLe(type: Value): Result<Row, KernelError> {
  const head = constructorHead(type);
  if (head === undefined || head.op !== OP_LE || head.args.length !== 2) {
    return err(
      kernelError(
        "farkas-not-a-le-hypothesis",
        `a Farkas hypothesis must have type Le s t, but this one has type ${describe(type)}`,
        { op: head?.op },
      ),
    );
  }
  const lhs = head.args[0]!;
  const rhs = head.args[1]!;
  const form = formSub(formOf(lhs, irrelevantOf), formOf(rhs, irrelevantOf));
  const a: Record<string, bigint> = {};
  for (const [key, atom] of form.atoms) a[key] = atom.coefficient;
  return ok({ a, b: -form.k });
}

/** A best-effort rendering of a value for diagnostics; never throws. */
function describe(value: Value): string {
  try {
    return keyOfValue(value, irrelevantOf);
  } catch {
    return "<unprintable>";
  }
}

