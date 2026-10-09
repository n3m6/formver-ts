// expect: reject
// `?:` is right-associative: when a < b the result is a, not b or c.
// A left-associative misparse ((a < b ? a : b) < c ? b : c) would satisfy this spec.
/**
 * @pre -1000 <= a && a <= 1000 && -1000 <= b && b <= 1000 && -1000 <= c && c <= 1000
 * @post result === b || result === c
 */
export function ternaryAssoc(a: number, b: number, c: number): number {
  return a < b ? a : b < c ? b : c;
}
