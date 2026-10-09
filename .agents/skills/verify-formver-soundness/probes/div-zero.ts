// expect: reject
// Division by zero gives Infinity, -Infinity or NaN, never a safe integer.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === 0
 */
export function divZero(x: number): number {
  return Math.floor(x / 0);
}
