// expect: reject
// Comments inside the body hide `+ 1` and a whole return; JavaScript returns x + 2.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x + 3
 */
export function commentTrap(x: number): number {
  // return x + 3;
  return x /* + 1 */ + 2;
}
