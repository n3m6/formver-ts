// expect: certify
// Control for comment-trap: the spec matches what JavaScript computes.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x + 2
 */
export function commentTrapOk(x: number): number {
  // return x + 3;
  return x /* + 1 */ + 2;
}
