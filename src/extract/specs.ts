/**
 * Spec resolution by parsing (specification 6.3).
 *
 * For every relative import a verified function uses, the imported `.ts`/`.mts` file is
 * **read and parsed**, never imported or executed: user code must not run during
 * verification (section 2, hard rules).  `specs.ts` is the only place in `src/extract/`
 * that touches the file system, and it is deliberately small so that the "no execution"
 * rule is easy to audit.
 *
 * Parsing gives the callee's declaration; `fragment.ts` maps it to the kernel type of an
 * `external` declaration, together with the sha256 of the file contents the type was
 * derived from.  Because only the signature is needed, **import cycles are harmless**: the
 * resolver never follows the imports of an imported file to build its signature (a type
 * alias imported by the callee is the one exception, and that graph is acyclic because
 * recursive type aliases are rejected).
 */
import { existsSync, readFileSync, statSync } from "node:fs";
import { dirname, isAbsolute, join, resolve } from "node:path";
import type { ExternalDecl, Term } from "../kernel/index";
import { parseFile } from "../syntax/parser";
import type { FnDecl, ParsedFile, TypeAliasDecl } from "../syntax/ast";

/** A parsed imported file together with the content hash its specs were derived from. */
export interface ImportedFile {
  /** Absolute path. */
  readonly path: string;
  readonly source: string;
  /** Lowercase hex sha256 of `source`. */
  readonly hash: string;
  readonly parsed: ParsedFile;
}

/** sha256 of the file contents, as the cache and `external` declarations key on it. */
export function contentHash(source: string): string {
  const hasher = new Bun.CryptoHasher("sha256");
  hasher.update(source);
  return hasher.digest("hex");
}

/** True when the specifier is a relative import (`./x` or `../x`). */
export function isRelativeSpecifier(specifier: string): boolean {
  return specifier.startsWith("./") || specifier.startsWith("../");
}

/**
 * Resolve a relative specifier against the importing file, trying `.ts`/`.mts` for an
 * extensionless specifier and `index.ts`/`index.mts` for a directory.  Returns an absolute
 * path, or `null` when nothing matches.
 */
export function resolveImportPath(fromFile: string, specifier: string): string | null {
  if (!isRelativeSpecifier(specifier)) return null;
  const base = resolve(dirname(fromFile), specifier);
  const candidates = [
    base,
    `${base}.ts`,
    `${base}.mts`,
    join(base, "index.ts"),
    join(base, "index.mts"),
  ];
  for (const candidate of candidates) {
    if (!existsSync(candidate)) continue;
    try {
      if (!statSync(candidate).isFile()) continue;
    } catch {
      continue;
    }
    return candidate;
  }
  return null;
}

export interface ResolveOk {
  readonly ok: true;
  readonly file: ImportedFile;
}

export interface ResolveErr {
  readonly ok: false;
  /** Human-readable reason, without a location (the caller attaches the span). */
  readonly message: string;
}

export type ResolveResult = ResolveOk | ResolveErr;

/**
 * Reads, parses and hashes imported files, caching by absolute path.  `read` is injectable
 * so tests can drive the resolver without touching the disk; the default uses
 * `node:fs.readFileSync`.
 */
export class SpecResolver {
  private readonly cache = new Map<string, ImportedFile>();
  private readonly read: (path: string) => string;

  constructor(read: (path: string) => string = (path) => readFileSync(path, "utf8")) {
    this.read = read;
  }

  /** Parse (or return the cached parse of) one file. */
  load(path: string): ResolveResult {
    const absolute = isAbsolute(path) ? path : resolve(path);
    const cached = this.cache.get(absolute);
    if (cached !== undefined) return { ok: true, file: cached };
    let source: string;
    try {
      source = this.read(absolute);
    } catch (error) {
      return { ok: false, message: `cannot read ${absolute}: ${String(error)}` };
    }
    const parsed = parseFile(absolute, source);
    const file: ImportedFile = { path: absolute, source, hash: contentHash(source), parsed };
    this.cache.set(absolute, file);
    return { ok: true, file };
  }

  /** Resolve a relative specifier from `fromFile` and parse the target. */
  resolve(fromFile: string, specifier: string): ResolveResult {
    if (!isRelativeSpecifier(specifier)) {
      return {
        ok: false,
        message:
          `only relative imports are allowed in verified functions; ` +
          `\`${specifier}\` is not relative`,
      };
    }
    const path = resolveImportPath(fromFile, specifier);
    if (path === null) return { ok: false, message: `cannot resolve \`${specifier}\` from ${fromFile}` };
    return this.load(path);
  }

  /** Drop the cache (used by tests that mutate files between runs). */
  clear(): void {
    this.cache.clear();
  }
}

/** The fully parsed declaration of a verified function, by name. */
export function specFunction(parsed: ParsedFile, name: string): FnDecl | undefined {
  return parsed.functions.find((fn) => fn.name === name);
}

/** A `type` alias declaration by name. */
export function specAlias(parsed: ParsedFile, name: string): TypeAliasDecl | undefined {
  return parsed.typeAliases.find((alias) => alias.name === name);
}

/**
 * An `external` declaration: another file's function, with the content hash of the file its
 * spec type was read from.  The strict CLI later confirms that every external declaration
 * was certified in its own file under the same hash (specification 6.1.5).
 */
export function externalDeclFor(name: string, type: Term, file: ImportedFile): ExternalDecl {
  return { kind: "external", name, type, source: { file: file.path, hash: file.hash } };
}
