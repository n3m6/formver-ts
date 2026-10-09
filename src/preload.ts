/**
 * Bun preload entry point, referenced by `bunfig.toml` both at the top level (for
 * `bun run`) and under `[test]` (for `bun test`): it registers the verifier plugin
 * (milestone 8, specification 6.7).
 *
 * The plugin skips this repository's own sources, so preloading it for `bun test` neither
 * verifies the test files that mention `@pre` in strings nor slows down the suite.
 */
import { plugin } from "bun";
import { depVerifyPlugin } from "./plugin";

plugin(depVerifyPlugin);

export {};
