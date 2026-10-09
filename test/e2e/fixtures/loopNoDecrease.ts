/**
 * The measure grows, so the back edge cannot prove `measure-decrease`.
 *
 * @pre 0 <= n && n <= 1000000
 * @post result >= 0
 */
export function loopNoDecrease(n: number): number {
  let i = 0;
  /**
   * @invariant 0 <= i && i <= n
   * @decreases i
   */
  while (i < n) {
    i = i + 1;
  }
  return 0;
}
