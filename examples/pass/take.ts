/**
 * @pre 0 <= n && n <= a.length
 * @post result.length === n
 */
export function take<T>(a: readonly T[], n: number): readonly T[] {
  return a.slice(0, n);
}
