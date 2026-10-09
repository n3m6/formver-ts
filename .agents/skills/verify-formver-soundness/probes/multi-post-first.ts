// expect: reject
// Every postcondition must hold. The false one comes first; a verifier that keeps only the last would certify.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x
 * @post result >= 0
 */
export function multiPostFirst(x: number): number {
  return x < 0 ? -x : x;
}
