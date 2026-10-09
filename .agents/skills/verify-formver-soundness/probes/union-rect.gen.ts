// Oracle input generator for union-rect.ts (and any one-parameter Shape function, such as examples/pass/shape.ts).
type Rng = { next(): number; int(lo: number, hi: number): number };

export default function generate(_fn: string, rng: Rng): unknown[] {
  const size = (): number => (rng.next() < 0.2 ? rng.int(-5, 5) : rng.int(0, 1_000_010));
  return [rng.next() < 0.5 ? { kind: "square", side: size() } : { kind: "rect", w: size(), h: size() }];
}
