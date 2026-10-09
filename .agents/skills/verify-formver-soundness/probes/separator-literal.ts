// expect: reject
// 1_000 is one thousand. A lexer that stops at the underscore reads 1.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x + 1
 */
export function separatorLiteral(x: number): number {
  return x + 1_000;
}
