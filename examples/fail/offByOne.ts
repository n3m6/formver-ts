/**
 * @pre 0 <= i && i <= a.length
 */
export function offByOne<T>(a: readonly T[], i: number): T {
  return a[i];
}
