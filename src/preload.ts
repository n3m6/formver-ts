/**
 * Bun preload entry point, referenced by `bunfig.toml` both at the top level
 * (for `bun run`) and under `[test]` (for `bun test`).
 *
 * Milestone 1 placeholder: it registers nothing yet. A later milestone replaces
 * this with the verifier plugin:
 *
 *   import { plugin } from "bun";
 *   import { depVerifyPlugin } from "./plugin";
 *   plugin(depVerifyPlugin);
 */
export {};
