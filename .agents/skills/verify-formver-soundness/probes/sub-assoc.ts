// expect: reject
// Subtraction is left-associative: the spec means (a - b) - c, the body computes a - (b - c).
/**
 * @pre -1000 <= a && a <= 1000 && -1000 <= b && b <= 1000 && -1000 <= c && c <= 1000
 * @post result === a - b - c
 */
export function subAssoc(a: number, b: number, c: number): number {
  return a - (b - c);
}
