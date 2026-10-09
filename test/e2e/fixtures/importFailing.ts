/**
 * Imports a failing example on purpose.  Run under `DEP_VERIFY_STRICT=1`, the plugin's
 * `onLoad` throws and this import rejects with the example's diagnostics
 * (`test/e2e/plugin.test.ts`); the file itself is never executed.
 */
import "../../../examples/fail/clampNoPre";

console.log("the failing example was imported despite strict mode");
