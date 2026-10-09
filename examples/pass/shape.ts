type Shape =
  | { readonly kind: "square"; readonly side: number }
  | { readonly kind: "rect"; readonly w: number; readonly h: number };

/**
 * @pre s.kind === "square" ? 0 <= s.side && s.side <= 1000000 : 0 <= s.w && s.w <= 1000000 && 0 <= s.h && s.h <= 1000000
 * @post result >= 0
 */
export function perimeter(s: Shape): number {
  switch (s.kind) {
    case "square":
      return 4 * s.side;
    case "rect":
      return 2 * (s.w + s.h);
  }
}
