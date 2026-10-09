// expect: reject
// 1e3 is one thousand. A lexer that stops at the `e` reads 1.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x + 1
 */
export function exponentLiteral(x: number): number {
  return x + 1e3;
}
