// expect: reject
// For a rect the perimeter is 2 * (w + h), not 4 * w.
type Shape =
  | { readonly kind: "square"; readonly side: number }
  | { readonly kind: "rect"; readonly w: number; readonly h: number };

/**
 * @pre s.kind === "square" ? 0 <= s.side && s.side <= 1000 : 0 <= s.w && s.w <= 1000 && 0 <= s.h && s.h <= 1000
 * @post result === 4 * (s.kind === "square" ? s.side : s.w)
 */
export function unionRect(s: Shape): number {
  switch (s.kind) {
    case "square":
      return 4 * s.side;
    case "rect":
      return 2 * (s.w + s.h);
  }
}
