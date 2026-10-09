// expect: reject
// 0x10 is sixteen. A lexer that reads it as 10 (or as 0 then x10) would certify this.
/**
 * @pre -1000 <= x && x <= 1000
 * @post result === x + 10
 */
export function hexLiteral(x: number): number {
  return x + 0x10;
}
