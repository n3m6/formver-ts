// expect: certify
// Control for ternary-assoc: true under the right-associative parse, false under the misparse.
/**
 * @pre -1000 <= a && a <= 1000 && -1000 <= b && b <= 1000 && -1000 <= c && c <= 1000
 * @post result <= b && (a < b ? result === a : result === b || result === c)
 */
export function ternaryAssocOk(a: number, b: number, c: number): number {
  return a < b ? a : b < c ? b : c;
}
