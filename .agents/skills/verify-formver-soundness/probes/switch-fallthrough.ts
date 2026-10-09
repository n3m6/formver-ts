// expect: reject
// Without `break`, case 1 falls through into case 2: k = 1 returns 2.
/**
 * @pre 0 <= k && k <= 2
 * @post result === k
 */
export function switchFallthrough(k: number): number {
  let r = 0;
  switch (k) {
    case 1:
      r = 1;
    case 2:
      r = 2;
      break;
    default:
      r = 0;
  }
  return r;
}
