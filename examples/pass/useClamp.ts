import { clamp } from "./clamp";

/**
 * @post 0 <= result && result <= 100
 */
export function percent(p: number): number {
  return clamp(p, 0, 100);
}
