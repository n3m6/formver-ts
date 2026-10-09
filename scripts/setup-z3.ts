/**
 * `bun run setup` — fetch the pinned Z3 release and unpack `libz3.so` into `.z3/`.
 *
 * Steps:
 *   1. If `DEP_VERIFY_LIBZ3` is set, use that shared library and skip everything else.
 *   2. If `.z3/libz3.so` already loads, print its version and stop (idempotent).
 *   3. Otherwise download the pinned zip into the gitignored `.z3/cache/`, verify its
 *      SHA-256, extract `bin/libz3.so` with the `unzip` binary, and print the version.
 *
 * This script is deliberately standalone. The full `bun:ffi` binding (contexts, push/pop,
 * queries, certificate search) lives in `src/vc/z3.ts` from a later milestone; here we only
 * need enough FFI to prove that the library loads and to report its version.
 *
 * Progress goes to stderr; the one machine-readable line, `Z3 <full version>`, goes to stdout.
 */
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, rmSync } from "node:fs";
import { join, resolve } from "node:path";
import { dlopen, FFIType } from "bun:ffi";

const Z3_VERSION = "5.1.0";
const ARCHIVE = `z3-${Z3_VERSION}-x64-glibc-2.39`;
const ZIP_URL = `https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/${ARCHIVE}.zip`;
const ZIP_SHA256 = "f47be8d27d3230e823bf1eeede2fe0abaca55bb78d0b59974370e6689a92284a";
const LIB_IN_ZIP = `${ARCHIVE}/bin/libz3.so`;

const repoRoot = resolve(import.meta.dir, "..");
const z3Dir = join(repoRoot, ".z3");
const libPath = join(z3Dir, "libz3.so");
const cacheDir = join(z3Dir, "cache");
const zipPath = join(cacheDir, `${ARCHIVE}.zip`);

function log(message: string): void {
  console.error(`[setup-z3] ${message}`);
}

function fail(message: string): never {
  console.error(`[setup-z3] error: ${message}`);
  process.exit(1);
}

/** Minimal version of the `openZ3` binding from the design (section 6.4). */
function openZ3(path: string): { version: () => string; close: () => void } {
  const z3 = dlopen(path, {
    Z3_get_full_version: { args: [], returns: FFIType.cstring },
    Z3_mk_config: { args: [], returns: FFIType.ptr },
    Z3_del_config: { args: [FFIType.ptr], returns: FFIType.void },
    Z3_mk_context: { args: [FFIType.ptr], returns: FFIType.ptr },
    Z3_del_context: { args: [FFIType.ptr], returns: FFIType.void },
    Z3_set_error_handler: { args: [FFIType.ptr, FFIType.ptr], returns: FFIType.void },
  });
  const cfg = z3.symbols.Z3_mk_config();
  const ctx = z3.symbols.Z3_mk_context(cfg);
  z3.symbols.Z3_del_config(cfg);
  // Without this, a Z3 error aborts the process instead of returning `(error "...")` text.
  z3.symbols.Z3_set_error_handler(ctx, null);
  return {
    version: () => String(z3.symbols.Z3_get_full_version()),
    close: () => {
      z3.symbols.Z3_del_context(ctx);
    },
  };
}

/** Load `path` and read Z3's full version, or explain why that failed. */
function tryLoad(
  path: string,
): { ok: true; version: string } | { ok: false; reason: string } {
  try {
    const z3 = openZ3(path);
    try {
      const version = z3.version();
      return version.length > 0 ? { ok: true, version } : { ok: false, reason: "empty version string" };
    } finally {
      z3.close();
    }
  } catch (err) {
    return { ok: false, reason: err instanceof Error ? err.message : String(err) };
  }
}

/** Print `Z3 <version>` for `path`; return false (with a log line) if it does not load. */
function report(path: string): boolean {
  const loaded = tryLoad(path);
  if (!loaded.ok) {
    log(`could not load ${path}: ${loaded.reason}`);
    return false;
  }
  console.log(/^z3\b/i.test(loaded.version) ? loaded.version : `Z3 ${loaded.version}`);
  return true;
}

async function sha256File(path: string): Promise<string> {
  const hasher = new Bun.CryptoHasher("sha256");
  hasher.update(await Bun.file(path).arrayBuffer());
  return hasher.digest("hex");
}

async function downloadZip(): Promise<void> {
  log(`downloading ${ZIP_URL}`);
  let response: Response;
  try {
    response = await fetch(ZIP_URL, { redirect: "follow" });
  } catch (err) {
    fail(`could not download ${ZIP_URL}: ${err instanceof Error ? err.message : String(err)}`);
  }
  if (!response.ok) {
    fail(`could not download ${ZIP_URL}: HTTP ${response.status} ${response.statusText}`);
  }
  mkdirSync(cacheDir, { recursive: true });
  await Bun.write(zipPath, new Uint8Array(await response.arrayBuffer()));
}

async function ensureVerifiedZip(): Promise<void> {
  if (existsSync(zipPath)) {
    const cached = await sha256File(zipPath);
    if (cached === ZIP_SHA256) {
      log(`using cached ${zipPath}`);
      return;
    }
    log(`cached archive failed verification (sha256 ${cached}); re-downloading`);
    rmSync(zipPath, { force: true });
  }
  await downloadZip();
  const digest = await sha256File(zipPath);
  if (digest !== ZIP_SHA256) {
    rmSync(zipPath, { force: true });
    fail(
      `SHA-256 mismatch for ${ZIP_URL}\n` +
        `  expected ${ZIP_SHA256}\n` +
        `  got      ${digest}\n` +
        `The downloaded archive was deleted. Check the release URL or set DEP_VERIFY_LIBZ3 ` +
        `to use a local libz3.so instead.`,
    );
  }
  log(`verified sha256 ${digest}`);
}

function extractLibz3(): void {
  mkdirSync(z3Dir, { recursive: true });
  const result = spawnSync("unzip", ["-o", "-j", zipPath, LIB_IN_ZIP, "-d", z3Dir], {
    encoding: "utf8",
  });
  if (result.error) {
    const code = (result.error as unknown as { code?: string }).code;
    if (code === "ENOENT") {
      fail(
        "the `unzip` binary was not found, so libz3.so cannot be extracted.\n" +
          "  Install it (for example `apt install unzip`), or\n" +
          "  set DEP_VERIFY_LIBZ3=/path/to/libz3.so to use an existing Z3 library.",
      );
    }
    fail(`could not run unzip: ${result.error.message}`);
  }
  if (result.status !== 0) {
    const detail = (result.stderr || result.stdout || "").trim();
    fail(`unzip exited with status ${result.status}${detail ? `: ${detail}` : ""}`);
  }
  if (!existsSync(libPath)) {
    fail(`unzip succeeded but ${libPath} is missing (looked for ${LIB_IN_ZIP} in the archive)`);
  }
}

const override = process.env.DEP_VERIFY_LIBZ3?.trim();
if (override) {
  const path = resolve(override);
  if (!existsSync(path)) {
    fail(`DEP_VERIFY_LIBZ3 points at ${path}, which does not exist`);
  }
  log(`using DEP_VERIFY_LIBZ3=${path} (skipping download)`);
  if (!report(path)) {
    fail(`DEP_VERIFY_LIBZ3=${path} could not be loaded as a Z3 shared library`);
  }
} else if (existsSync(libPath) && report(libPath)) {
  log(`${libPath} already present and loadable; nothing to do`);
} else {
  if (existsSync(libPath)) {
    log(`${libPath} exists but does not load; re-downloading`);
    rmSync(libPath, { force: true });
  }
  await ensureVerifiedZip();
  extractLibz3();
  log(`extracted ${libPath}`);
  if (!report(libPath)) {
    fail(`${libPath} was extracted but could not be loaded`);
  }
}
