/**
 * A deliberately failing function, used to check that a caller of an uncertified function
 * is marked: `x + y` may leave the safe integer range and the postcondition needs a bound
 * the specification does not give.
 *
 * @post result === x + y
 */
export function badAdd(x: number, y: number): number {
  return x + y;
}
