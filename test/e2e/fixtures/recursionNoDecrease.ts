/**
 * The measure is `lo`, which the recursive call does not change: the call site's
 * `measure-decrease` obligation must report a counterexample (and every other obligation of
 * this function is certified, so the diagnostic is unambiguous).
 *
 * @pre 0 <= n && n <= 1000000
 * @pre 0 <= lo && lo <= n
 * @post 0 <= result
 * @decreases lo
 */
export function spin(n: number, lo: number): number {
  if (n === lo) return lo;
  return spin(n - 1, lo);
}
