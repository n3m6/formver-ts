/**
 * A second, independent loop acceptance case: the carried state is one variable and the
 * measure is `n - i`, so both back-edge measure obligations need the invariant and the
 * loop condition.
 *
 * @pre 0 <= n && n <= 1000000
 * @post 0 <= result && result <= n
 */
export function loopCountUp(n: number): number {
  let i = 0;
  /**
   * @invariant 0 <= i && i <= n
   * @decreases n - i
   */
  while (i < n) {
    i = i + 1;
  }
  return i;
}
