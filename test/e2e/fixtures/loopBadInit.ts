/**
 * The invariant is false on entry (`i = n`, so `i < n` does not hold): the loop's
 * `invariant-init` obligation must report a counterexample.
 *
 * @pre 0 <= n && n <= 1000000
 * @post result >= 0
 */
export function loopBadInit(n: number): number {
  let i = n;
  /**
   * @invariant 0 <= i && i < n
   * @decreases i
   */
  while (i > 0) {
    i = i - 1;
  }
  return 0;
}
