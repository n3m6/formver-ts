// expect: reject
// A default applies only when the caller omits y; every caller here passes it.
/**
 * @pre -1000 <= x && x <= 1000 && -1000 <= y && y <= 1000
 * @post result === x + 5
 */
export function defaultParam(x: number, y: number = 5): number {
  return x + y;
}
