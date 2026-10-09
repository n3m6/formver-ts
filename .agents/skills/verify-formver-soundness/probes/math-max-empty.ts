// expect: reject
// Math.max() with no arguments is -Infinity: the postcondition holds but the result is not a safe integer.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result <= x
 */
export function mathMaxEmpty(x: number): number {
  return Math.max();
}
