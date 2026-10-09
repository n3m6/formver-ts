import { badAdd } from "./uncertified";

/**
 * The caller only repeats the callee's postcondition, so it verifies even though `badAdd`
 * itself does not: an uncertified function's spec may still be used, and the caller is
 * marked as depending on it.
 *
 * @pre x >= 0
 * @post result === x + y
 */
export function callBadAdd(x: number, y: number): number {
  return badAdd(x, y);
}
