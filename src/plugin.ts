/**
 * The Bun plugin (specification 6.7, milestone 8).
 *
 * `onLoad` is **synchronous** (section 3.1 point 5) and returns `{ contents, loader: "ts" }`
 * for every file it accepts, because a runtime plugin cannot decline a file (point 2).  Three
 * gates keep the cost off ordinary files:
 *
 *   1. the filter `/^(?!.*\/node_modules\/).*\.(ts|mts)$/` (points 1 and 3),
 *   2. `isOwnSource`: this repository's own `src/`, `test/` and `scripts/` are never verified —
 *      our sources mention `@pre` inside strings and tests, and the plugin must not treat
 *      those as specs,
 *   3. a quick reject: no `@pre`/`@post`/`@decreases` anywhere in the text.
 *
 * The same object works for `bun run` (via `src/preload.ts`) and for
 * `Bun.build({ plugins: [depVerifyPlugin] })`.  In strict mode (`DEP_VERIFY_STRICT=1`) a file
 * that does not verify rejects the import (or fails the build); otherwise diagnostics are
 * warned about and the runtime checks the plan asks for are injected.
 */
import type { BunPlugin } from "bun";
import { readFileSync } from "node:fs";
import { isAbsolute, relative, resolve, sep } from "node:path";
import { verifyCached, type CachedVerifyReport } from "./cache";
import { formatDiagnostics } from "./diagnostics";
import { inject, InjectionError } from "./inject/inject";

/** The repository root, resolved from this file rather than from the process cwd. */
export const REPO_ROOT: string = resolve(import.meta.dir, "..");

/** Sections of this repository the plugin never verifies (see the header). */
const OWN_DIRECTORIES: readonly string[] = ["src", "test", "scripts"];

/** A source is worth verifying only when it mentions a function spec tag. */
const SPEC_TAG = /@(pre|post|decreases)\b/;

/** Files the plugin intercepts: TypeScript, never inside `node_modules` (section 3.1). */
const FILTER = /^(?!.*\/node_modules\/).*\.(ts|mts)$/;

/** True for this repository's own sources (and its tests and scripts). */
export function isOwnSource(path: string): boolean {
  const rel = relative(REPO_ROOT, resolve(path));
  if (rel === "" || rel.startsWith("..") || isAbsolute(rel)) return false;
  return OWN_DIRECTORIES.some((directory) => rel.startsWith(`${directory}${sep}`));
}

/** The message a strict-mode rejection carries: every diagnostic, or a summary. */
export function strictFailureMessage(result: CachedVerifyReport): string {
  if (result.diagnostics.length > 0) return formatDiagnostics(result.diagnostics);
  const uncertified = result.functions.filter((fn) => !fn.certified).map((fn) => fn.name);
  return (
    `${result.path}: strict verification failed` +
    (uncertified.length === 0 ? "" : `: \`${uncertified.join("`, `")}\` is not kernel-certified`)
  );
}

export const depVerifyPlugin: BunPlugin = {
  name: "dep-verify",
  setup(builder) {
    builder.onLoad({ filter: FILTER }, (args) => {
      const source = readFileSync(args.path, "utf8");
      if (isOwnSource(args.path) || !SPEC_TAG.test(source)) {
        return { contents: source, loader: "ts" };
      }
      const strict = process.env.DEP_VERIFY_STRICT === "1";
      const result = verifyCached(args.path, source, { strict });
      if (strict && !result.ok) throw new Error(strictFailureMessage(result));
      if (result.diagnostics.length > 0) console.warn(formatDiagnostics(result.diagnostics));
      try {
        const contents = inject(source, result.plan, {
          production: process.env.NODE_ENV === "production",
          path: args.path,
        });
        return { contents, loader: "ts" };
      } catch (error) {
        // Failing loudly beats handing Bun code whose checks are half-injected.
        if (error instanceof InjectionError) throw new Error(error.message);
        throw error;
      }
    });
  },
};
