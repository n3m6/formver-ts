// expect: reject
// When n === 0 the false branch calls g(-1), breaking g's precondition (visible to the oracle under the plugin).
/**
 * @pre 0 <= m && m <= 10
 */
function g(m: number): number {
  return m;
}

/**
 * @pre 0 <= n && n <= 10
 * @post -1 <= result && result <= 10
 */
export function neqCall(n: number): number {
  if (n !== 0) return 0;
  return g(n - 1);
}
