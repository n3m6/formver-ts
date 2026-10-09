/**
 * The invariant `i <= n` is not preserved: the body steps by two, so the back edge can
 * leave the invariant (`invariant-preserve`).
 *
 * @pre 0 <= n && n <= 1000000
 * @post 0 <= result && result <= n
 */
export function loopBadPreserve(n: number): number {
  let i = 0;
  /**
   * @invariant 0 <= i && i <= n
   * @decreases n - i
   */
  while (i < n) {
    i = i + 2;
  }
  return i;
}
