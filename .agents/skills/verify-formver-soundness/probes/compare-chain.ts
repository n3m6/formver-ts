// expect: reject
// `a < b < c` is `(a < b) < c`: a boolean coerced to 0 or 1, then compared with c.
// It is not the mathematical chain; a = 5, b = 1, c = 1 returns 1.
/**
 * @pre -1000 <= a && a <= 1000 && -1000 <= b && b <= 1000 && -1000 <= c && c <= 1000
 * @post result === (a < b && b < c ? 1 : 0)
 */
export function compareChain(a: number, b: number, c: number): number {
  // @ts-ignore: TypeScript rejects boolean < number, Bun runs it
  return a < b < c ? 1 : 0;
}
