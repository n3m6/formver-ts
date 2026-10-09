// expect: certify
// Control for floor-trunc: Math.floor rounds down, so 2 * floor(x / 2) <= x always.
/**
 * @pre -1000 <= x && x <= 1000
 * @post 2 * result <= x
 */
export function floorOk(x: number): number {
  return Math.floor(x / 2);
}
