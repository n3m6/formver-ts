// expect: certify
// `a[i]` is in the README's spec grammar, so an index inside a postcondition should verify.
/**
 * @pre 2 <= a.length
 * @post result === a[1]
 */
export function second(a: readonly number[]): number {
  return a[1];
}
