/**
 * Regression fixture (fixc 2): loops whose `@invariant` and `@post` use `===`.
 *
 * Not a test file: `test/e2e/fixc-loop-equality.test.ts` verifies it and differential-tests
 * it.  The three loops cover both orientations of the equality against the loop-carried
 * state — `acc === i` (the tuple component on the right) and `i === acc` (on the left) — and
 * both loop forms, `while` and `for`.
 */

/**
 * @pre 0 <= n && n <= 100
 * @post result === n
 */
export function countTo(n: number): number {
  let acc = 0;
  let i = 0;
  /**
   * @invariant 0 <= i && i <= n && acc === i
   * @decreases n - i
   */
  while (i < n) {
    acc = acc + 1;
    i = i + 1;
  }
  return acc;
}

/**
 * @pre 0 <= n && n <= 100
 * @post result === 2 * n
 */
export function doubleTo(n: number): number {
  let acc = 0;
  let i = 0;
  /**
   * @invariant 0 <= i && i <= n && acc === 2 * i
   * @decreases n - i
   */
  for (; i < n; i = i + 1) {
    acc = acc + 2;
  }
  return acc;
}

/**
 * @pre 0 <= n && n <= 100
 * @post result === n
 */
export function swappedAssertion(n: number): number {
  let i = 0;
  let acc = 0;
  /**
   * @invariant 0 <= i && i <= n && i === acc
   * @decreases n - i
   */
  while (i < n) {
    i = i + 1;
    acc = acc + 1;
  }
  return acc;
}
