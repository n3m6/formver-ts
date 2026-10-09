// expect: certify
// Control for sub-assoc: the same spec with the body written the way the spec parses.
/**
 * @pre -1000 <= a && a <= 1000 && -1000 <= b && b <= 1000 && -1000 <= c && c <= 1000
 * @post result === a - b - c
 */
export function subAssocOk(a: number, b: number, c: number): number {
  return a - b - c;
}
