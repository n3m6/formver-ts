// expect: reject
// The inner `const x` shadows the parameter: for x > 0 the function returns 0.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x
 */
export function shadow(x: number): number {
  if (x > 0) {
    const x = 0;
    return x;
  }
  return x;
}
