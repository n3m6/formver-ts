// expect: reject
// The false arm of a `!==` conditional is taken when n === 0 and yields 2.
/**
 * @pre 0 <= n && n <= 10
 * @post result === 1
 */
export function neqTernary(n: number): number {
  return n !== 0 ? 1 : 2;
}
