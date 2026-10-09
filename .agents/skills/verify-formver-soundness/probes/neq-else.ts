// expect: reject
// The false branch of `!==` runs when n === 0 and returns 2.
/**
 * @pre 0 <= n && n <= 10
 * @post result === 1
 */
export function neqElse(n: number): number {
  if (n !== 0) return 1;
  return 2;
}
