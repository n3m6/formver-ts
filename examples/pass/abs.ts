/**
 * @post result >= 0
 * @post result === x || result === -x
 */
export function abs(x: number): number {
  return x < 0 ? -x : x;
}
