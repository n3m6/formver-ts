import { safeGet } from "../pass/safeGet";

console.log(safeGet([10, 20, 30], 1));
console.log(safeGet([10, 20, 30], 5)); // PreconditionError, reported at safeGet.ts's function line
