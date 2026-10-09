// expect: reject
// ASI: `return` followed by a newline returns undefined; `x + 1` is dead code.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x + 1
 */
export function asiReturn(x: number): number {
  return
    x + 1;
}
