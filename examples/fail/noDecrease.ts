/**
 * @pre 0 <= n
 * @decreases n
 */
export function spin(n: number): number {
  if (n === 0) return 0;
  return spin(n);
}
