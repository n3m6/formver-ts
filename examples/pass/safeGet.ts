/**
 * @pre 0 <= i && i < a.length
 */
export function safeGet<T>(a: readonly T[], i: number): T {
  return a[i];
}
