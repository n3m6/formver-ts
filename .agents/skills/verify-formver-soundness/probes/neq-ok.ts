// expect: certify
// Control for the neq probes: both arms of `!==` meet this spec.
/**
 * @pre 0 <= n && n <= 10
 * @post 1 <= result && result <= 2
 */
export function neqOk(n: number): number {
  if (n !== 0) return 1;
  return 2;
}
