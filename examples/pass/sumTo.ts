/**
 * @pre 0 <= n && n <= 1000000
 * @post 0 <= result && result <= n * 1000000
 * @decreases n
 */
export function sumTo(n: number): number {
  if (n === 0) return 0;
  return n + sumTo(n - 1);
}
