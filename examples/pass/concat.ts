/**
 * @pre a.length + b.length <= 4294967295
 * @post result.length === a.length + b.length
 */
export function concat<T>(a: readonly T[], b: readonly T[]): readonly T[] {
  return [...a, ...b];
}
