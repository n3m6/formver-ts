// expect: reject
// `x - -1` is x + 1.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x - 1
 */
export function minusMinus(x: number): number {
  return x - -1;
}
