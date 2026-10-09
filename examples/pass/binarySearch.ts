/**
 * @post -1 <= result && result < a.length
 */
export function binarySearch(a: readonly number[], target: number): number {
  let lo = 0;
  let hi = a.length;
  /**
   * @invariant 0 <= lo && lo <= hi && hi <= a.length
   * @decreases hi - lo
   */
  while (lo < hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (a[mid] === target) return mid;
    if (a[mid] < target) {
      lo = mid + 1;
    } else {
      hi = mid;
    }
  }
  return -1;
}
