// expect: reject
// The comma operator evaluates to its right operand: this returns 0.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x
 */
export function commaOperator(x: number): number {
  // @ts-ignore: TypeScript flags the unused left operand, Bun runs it
  return (x, 0);
}
