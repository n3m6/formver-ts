// expect: reject
// Every postcondition must hold. The false one comes last; a verifier that keeps only the first would certify.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result >= 0
 * @post result === x
 */
export function multiPostLast(x: number): number {
  return x < 0 ? -x : x;
}
