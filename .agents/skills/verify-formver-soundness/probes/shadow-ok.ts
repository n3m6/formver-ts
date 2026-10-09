// expect: certify
// Control for shadow: the spec states what the shadowing really does.
/**
 * @pre -1000 <= x && x <= 1000
 * @post x > 0 ? result === 0 : result === x
 */
export function shadowOk(x: number): number {
  if (x > 0) {
    const x = 0;
    return x;
  }
  return x;
}
