// expect: reject
// x + 2 leaves the safe range at x = 2^53 - 1 and rounds; subtracting 2 does not undo it.
/**
 * @pre 0 <= x && x <= 9007199254740991
 * @post result === x
 */
export function floatRounding(x: number): number {
  return x + 2 - 2;
}
