/**
 * One annotated function per rejected construct.  Each comment above a function
 * names the diagnostic milestone 5 must produce: a located `error[fragment]` at
 * the construct, not a parse error.
 */

// error[fragment]: `any` is not an accepted type
/**
 * @post result === 1
 */
export function anyParameter(x: any): number {
  return 1;
}

// error[fragment]: `as` casts are not allowed
/**
 * @post result === x
 */
export function asCast(x: number): number {
  return x as number;
}

// error[fragment]: mutating a parameter is not allowed
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function parameterMutation(x: number): number {
  x = x + 1;
  return x;
}

// error[fragment]: `/` is only allowed as Math.floor(e / k) or Math.trunc(e / k)
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function plainDivision(x: number): number {
  return x / 2;
}

// error[fragment]: `throw` is not allowed
/**
 * @post result >= 0
 */
export function throwStatement(x: number): number {
  throw new Error("not in the fragment");
}

// error[fragment]: float literals are not allowed
/**
 * @post result > 0
 */
export function floatLiteral(): number {
  return 1.5;
}

// error[fragment]: `this` is not allowed
/**
 * @post result === 0
 */
export function thisExpression(): number {
  return this;
}

// error[fragment]: `%` is not allowed
/**
 * @pre x >= 0
 * @post result >= 0
 */
export function moduloOperator(x: number): number {
  return x % 2;
}
