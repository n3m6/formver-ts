/**
 * A recursive function with a four-component argument tuple (two parameters and their two
 * `InRange` proofs) and two preconditions: every recursive call needs the callee's
 * preconditions at the new arguments (`pre-call`), the non-negativity of the new measure and
 * its decrease.
 *
 * @pre 0 <= n && n <= 1000000
 * @pre 0 <= lo && lo <= n
 * @post 0 <= result
 * @decreases n
 */
export function countDown(n: number, lo: number): number {
  if (n === lo) return lo;
  return countDown(n - 1, lo);
}
