// expect: reject
// Math.trunc rounds toward zero: x = -3 gives -1, and 2 * -1 <= -3 is false.
/**
 * @pre -1000 <= x && x <= 1000
 * @post 2 * result <= x
 */
export function floorTrunc(x: number): number {
  return Math.trunc(x / 2);
}
