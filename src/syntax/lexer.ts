/**
 * Whole-file tokenizer.
 *
 * The lexer is deliberately a *JavaScript* lexer, not a fragment lexer: it must
 * produce a well-formed token stream for any `.ts` file so that the parser can
 * skip unannotated top-level code by matching braces.  Nothing here decides
 * whether a construct belongs to the verified fragment.
 *
 * Scope:
 *   - line comments (dropped) and block comments (dropped), except JSDoc blocks
 *     (`/** … *\/`), which are kept as `jsdoc` tokens for `jsdoc.ts`;
 *   - string literals with all three quote kinds and escapes;
 *   - template literals with arbitrarily nested `${ … }` (inner token streams
 *     are lexed recursively and stored on the token);
 *   - regex literals versus division, decided from the previous significant
 *     token, esbuild-style;
 *   - numeric literals: decimal integers and floats, hex/binary/octal, numeric
 *     separators and bigint suffixes, each flagged (floats are *not* rejected
 *     here; milestone 5 does that);
 *   - identifiers and reserved words;
 *   - every punctuator, plus a one-character fallback so that unusual input
 *     (`@decorator`, `#private`, `\u` escapes) still tokenizes.
 *
 * Unterminated strings, templates, regexes and block comments are reported as
 * located `parse` diagnostics and recovered from; the lexer never throws.
 */

import { type Diagnostic, type Span, offsetToPosition, sortDiagnostics } from "../diagnostics";

export type TokenKind =
  | "ident"
  | "keyword"
  | "number"
  | "string"
  | "template"
  | "regex"
  | "punct"
  | "jsdoc"
  | "eof";

export interface NumericInfo {
  isFloat: boolean;
  isBigInt: boolean;
  base: "decimal" | "hex" | "binary" | "octal";
}

export type TemplatePart =
  | { type: "text"; raw: string; span: Span }
  | { type: "expr"; tokens: Token[]; span: Span };

export interface RegexInfo {
  pattern: string;
  flags: string;
}

export interface Token {
  kind: TokenKind;
  /** Verbatim source slice. */
  text: string;
  span: Span;
  numeric?: NumericInfo;
  /** Present on `template` tokens: alternating text and `${ … }` parts. */
  template?: TemplatePart[];
  /** Present on `regex` tokens. */
  regex?: RegexInfo;
}

export interface LexResult {
  tokens: Token[];
  diagnostics: Diagnostic[];
}

/** Reserved words (contextual keywords such as `let`, `as`, `type` stay `ident`). */
export const KEYWORDS: ReadonlySet<string> = new Set([
  "await",
  "break",
  "case",
  "catch",
  "class",
  "const",
  "continue",
  "debugger",
  "default",
  "delete",
  "do",
  "else",
  "enum",
  "export",
  "extends",
  "false",
  "finally",
  "for",
  "function",
  "if",
  "import",
  "in",
  "instanceof",
  "new",
  "null",
  "return",
  "super",
  "switch",
  "this",
  "throw",
  "true",
  "try",
  "typeof",
  "var",
  "void",
  "while",
  "with",
  "yield",
]);

/** Keywords that may end an expression, so a following `/` is division. */
const EXPR_ENDING_KEYWORDS: ReadonlySet<string> = new Set(["this", "super", "true", "false", "null"]);

/** Punctuators after which a `/` is division rather than a regex. */
const EXPR_ENDING_PUNCT: ReadonlySet<string> = new Set([")", "]", "}", "++", "--"]);

const PUNCTUATORS: readonly string[] = [
  ">>>=",
  "...",
  "===",
  "!==",
  "**=",
  "<<=",
  ">>=",
  ">>>",
  "&&=",
  "||=",
  "??=",
  "=>",
  "==",
  "!=",
  "<=",
  ">=",
  "&&",
  "||",
  "??",
  "**",
  "++",
  "--",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "&=",
  "|=",
  "^=",
  "<<",
  ">>",
  "?.",
  "{",
  "}",
  "(",
  ")",
  "[",
  "]",
  ";",
  ",",
  "<",
  ">",
  "+",
  "-",
  "*",
  "/",
  "%",
  "&",
  "|",
  "^",
  "!",
  "~",
  "?",
  ":",
  "=",
  ".",
  "@",
  "#",
];

function isWhitespace(ch: string): boolean {
  return (
    ch === " " ||
    ch === "\t" ||
    ch === "\n" ||
    ch === "\r" ||
    ch === "\f" ||
    ch === "\v" ||
    ch === "\u00a0" ||
    ch === "\ufeff" ||
    ch === "\u2028" ||
    ch === "\u2029"
  );
}

function isDigit(ch: string | undefined): boolean {
  return ch !== undefined && ch >= "0" && ch <= "9";
}

function isHexDigit(ch: string | undefined): boolean {
  return ch !== undefined && ((ch >= "0" && ch <= "9") || (ch >= "a" && ch <= "f") || (ch >= "A" && ch <= "F"));
}

function isIdentStart(ch: string | undefined): boolean {
  if (ch === undefined) return false;
  if (ch === "$" || ch === "_") return true;
  if (ch >= "a" && ch <= "z") return true;
  if (ch >= "A" && ch <= "Z") return true;
  return ch.charCodeAt(0) > 0x7f;
}

function isIdentContinue(ch: string | undefined): boolean {
  return isIdentStart(ch) || isDigit(ch);
}

export function isWord(token: Token): boolean {
  return token.kind === "ident" || token.kind === "keyword";
}

/** True for an identifier or keyword token with the given text (or any, if omitted). */
export function isWordToken(token: Token, text?: string): boolean {
  return isWord(token) && (text === undefined || token.text === text);
}

export function isKeyword(token: Token, text?: string): boolean {
  return token.kind === "keyword" && (text === undefined || token.text === text);
}

export function isPunct(token: Token, text?: string): boolean {
  return token.kind === "punct" && (text === undefined || token.text === text);
}

class Lexer {
  private pos = 0;
  private line = 1;
  private col = 1;
  private readonly tokens: Token[] = [];
  private readonly diagnostics: Diagnostic[] = [];
  /** Previous significant (non-JSDoc) token, for the regex/division decision. */
  private prev: Token | null = null;

  constructor(
    private readonly source: string,
    private readonly file: string,
  ) {}

  run(): LexResult {
    if (this.source.startsWith("#!")) this.skipToLineEnd();
    this.lexTokens(this.tokens, false);
    const eofSpan: Span = {
      file: this.file,
      line: this.line,
      col: this.col,
      offset: this.pos,
      endOffset: this.pos,
    };
    this.tokens.push({ kind: "eof", text: "", span: eofSpan });
    return { tokens: this.tokens, diagnostics: sortDiagnostics(this.diagnostics) };
  }

  // ---------------------------------------------------------------- positions

  private advance(): string {
    const ch = this.source[this.pos]!;
    this.pos += 1;
    if (ch === "\n") {
      this.line += 1;
      this.col = 1;
    } else {
      this.col += 1;
    }
    return ch;
  }

  private skipToLineEnd(): void {
    while (this.pos < this.source.length && this.source[this.pos] !== "\n") this.advance();
  }

  private span(startOffset: number, startLine: number, startCol: number): Span {
    return { file: this.file, line: startLine, col: startCol, offset: startOffset, endOffset: this.pos };
  }

  private error(message: string, startOffset: number, startLine: number, startCol: number): void {
    this.diagnostics.push({
      kind: "parse",
      severity: "error",
      span: this.span(startOffset, startLine, startCol),
      message,
    });
  }

  private push(out: Token[], token: Token): void {
    out.push(token);
    if (token.kind !== "jsdoc" && token.kind !== "eof") this.prev = token;
  }

  private charAt(offset: number): string | undefined {
    return this.source[offset];
  }

  // ------------------------------------------------------------------- driver

  /**
   * Lex tokens into `out`.  With `template` set, the scan stops at the `}` that
   * closes the enclosing `${ … }` (that `}` is left unconsumed); braces inside
   * the expression are tracked so object literals do not end it early.
   */
  private lexTokens(out: Token[], template: boolean): void {
    let depth = 0;
    for (;;) {
      this.skipTrivia(out);
      if (this.pos >= this.source.length) return;
      const ch = this.source[this.pos]!;
      if (template) {
        if (ch === "}") {
          if (depth === 0) return;
          depth -= 1;
        } else if (ch === "{") {
          depth += 1;
        }
      }
      this.lexOne(out);
    }
  }

  private skipTrivia(out: Token[]): void {
    for (;;) {
      const ch = this.source[this.pos];
      if (ch === undefined) return;
      if (isWhitespace(ch)) {
        this.advance();
        continue;
      }
      if (ch === "/" && this.charAt(this.pos + 1) === "/") {
        this.skipToLineEnd();
        continue;
      }
      if (ch === "/" && this.charAt(this.pos + 1) === "*") {
        const isDoc = this.charAt(this.pos + 2) === "*" && this.charAt(this.pos + 3) !== "/";
        const startOffset = this.pos;
        const startLine = this.line;
        const startCol = this.col;
        this.advance();
        this.advance();
        let terminated = false;
        while (this.pos < this.source.length) {
          if (this.source[this.pos] === "*" && this.charAt(this.pos + 1) === "/") {
            this.advance();
            this.advance();
            terminated = true;
            break;
          }
          this.advance();
        }
        if (!terminated) {
          this.error("unterminated block comment", startOffset, startLine, startCol);
          return;
        }
        if (isDoc) {
          const token: Token = {
            kind: "jsdoc",
            text: this.source.slice(startOffset, this.pos),
            span: this.span(startOffset, startLine, startCol),
          };
          this.push(out, token);
        }
        continue;
      }
      return;
    }
  }

  private lexOne(out: Token[]): void {
    const ch = this.source[this.pos]!;
    if (ch === '"' || ch === "'") {
      this.lexString(out, ch);
      return;
    }
    if (ch === "`") {
      this.lexTemplate(out);
      return;
    }
    if (isDigit(ch) || (ch === "." && isDigit(this.charAt(this.pos + 1)))) {
      this.lexNumber(out);
      return;
    }
    if (isIdentStart(ch)) {
      this.lexIdent(out);
      return;
    }
    if (ch === "/" && this.regexAllowed()) {
      this.lexRegex(out);
      return;
    }
    this.lexPunct(out);
  }

  // ----------------------------------------------------------------- literals

  private lexString(out: Token[], quote: string): void {
    const startOffset = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    this.advance();
    let terminated = false;
    while (this.pos < this.source.length) {
      const ch = this.source[this.pos]!;
      if (ch === "\\") {
        this.advance();
        if (this.pos < this.source.length) this.advance();
        continue;
      }
      if (ch === quote) {
        this.advance();
        terminated = true;
        break;
      }
      if (ch === "\n") break; // JS strings cannot span raw newlines
      this.advance();
    }
    if (!terminated) {
      this.error("unterminated string literal", startOffset, startLine, startCol);
    }
    const token: Token = {
      kind: "string",
      text: this.source.slice(startOffset, this.pos),
      span: this.span(startOffset, startLine, startCol),
    };
    this.push(out, token);
  }

  private lexTemplate(out: Token[]): void {
    const startOffset = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    this.advance(); // backtick
    const parts: TemplatePart[] = [];
    let textStart = this.pos;
    let textLine = this.line;
    let textCol = this.col;
    const flushText = (): void => {
      if (this.pos > textStart) {
        parts.push({
          type: "text",
          raw: this.source.slice(textStart, this.pos),
          span: {
            file: this.file,
            line: textLine,
            col: textCol,
            offset: textStart,
            endOffset: this.pos,
          },
        });
      }
    };
    let terminated = false;
    while (this.pos < this.source.length) {
      const ch = this.source[this.pos]!;
      if (ch === "\\") {
        this.advance();
        if (this.pos < this.source.length) this.advance();
        continue;
      }
      if (ch === "`") {
        flushText();
        this.advance();
        terminated = true;
        break;
      }
      if (ch === "$" && this.charAt(this.pos + 1) === "{") {
        flushText();
        this.advance();
        this.advance();
        const exprStart = this.pos;
        const exprStartLine = this.line;
        const exprStartCol = this.col;
        const savedPrev = this.prev;
        this.prev = null; // a `${ … }` always starts a fresh expression
        const inner: Token[] = [];
        this.lexTokens(inner, true);
        this.prev = savedPrev;
        // Sub-parsers need a terminating token; the `}` is left unconsumed above.
        inner.push({
          kind: "eof",
          text: "",
          span: {
            file: this.file,
            line: this.line,
            col: this.col,
            offset: this.pos,
            endOffset: this.pos,
          },
        });
        const exprSpan = this.span(exprStart, exprStartLine, exprStartCol);
        if (this.source[this.pos] === "}") {
          this.advance();
        } else {
          this.error("unterminated template expression", startOffset, startLine, startCol);
        }
        parts.push({ type: "expr", tokens: inner, span: exprSpan });
        textStart = this.pos;
        textLine = this.line;
        textCol = this.col;
        continue;
      }
      this.advance();
    }
    if (!terminated) this.error("unterminated template literal", startOffset, startLine, startCol);
    const token: Token = {
      kind: "template",
      text: this.source.slice(startOffset, this.pos),
      span: this.span(startOffset, startLine, startCol),
      template: parts,
    };
    this.push(out, token);
  }

  private lexRegex(out: Token[]): void {
    const startOffset = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    this.advance(); // slash
    let inClass = false;
    let terminated = false;
    while (this.pos < this.source.length) {
      const ch = this.source[this.pos]!;
      if (ch === "\\") {
        this.advance();
        if (this.pos < this.source.length) this.advance();
        continue;
      }
      if (ch === "\n") break;
      if (ch === "[") inClass = true;
      else if (ch === "]") inClass = false;
      else if (ch === "/" && !inClass) {
        this.advance();
        terminated = true;
        break;
      }
      this.advance();
    }
    let flags = "";
    while (isIdentContinue(this.charAt(this.pos))) flags += this.advance();
    if (!terminated) this.error("unterminated regular expression literal", startOffset, startLine, startCol);
    const text = this.source.slice(startOffset, this.pos);
    const lastSlash = text.lastIndexOf("/");
    const pattern = terminated ? text.slice(1, lastSlash) : text.slice(1);
    const token: Token = {
      kind: "regex",
      text,
      span: this.span(startOffset, startLine, startCol),
      regex: { pattern, flags: terminated ? flags : "" },
    };
    this.push(out, token);
  }

  private lexNumber(out: Token[]): void {
    const startOffset = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    let isFloat = false;
    let base: NumericInfo["base"] = "decimal";

    const readDigits = (predicate: (ch: string | undefined) => boolean): void => {
      while (true) {
        const ch = this.charAt(this.pos);
        if (predicate(ch)) {
          this.advance();
          continue;
        }
        if (ch === "_") {
          this.advance();
          continue;
        }
        break;
      }
    };

    if (this.source[this.pos] === "0" && (this.charAt(this.pos + 1) === "x" || this.charAt(this.pos + 1) === "X")) {
      base = "hex";
      this.advance();
      this.advance();
      readDigits(isHexDigit);
    } else if (
      this.source[this.pos] === "0" &&
      (this.charAt(this.pos + 1) === "b" || this.charAt(this.pos + 1) === "B")
    ) {
      base = "binary";
      this.advance();
      this.advance();
      readDigits((ch) => ch === "0" || ch === "1");
    } else if (
      this.source[this.pos] === "0" &&
      (this.charAt(this.pos + 1) === "o" || this.charAt(this.pos + 1) === "O")
    ) {
      base = "octal";
      this.advance();
      this.advance();
      readDigits((ch) => ch !== undefined && ch >= "0" && ch <= "7");
    } else {
      readDigits(isDigit);
      if (this.charAt(this.pos) === "." && this.charAt(this.pos + 1) !== ".") {
        isFloat = true;
        this.advance();
        readDigits(isDigit);
      }
      const e = this.charAt(this.pos);
      if (e === "e" || e === "E") {
        const next = this.charAt(this.pos + 1);
        const afterNext = this.charAt(this.pos + 2);
        const hasDigits = isDigit(next) || ((next === "+" || next === "-") && isDigit(afterNext));
        if (hasDigits) {
          isFloat = true;
          this.advance();
          if (this.charAt(this.pos) === "+" || this.charAt(this.pos) === "-") this.advance();
          readDigits(isDigit);
        }
      }
    }

    let isBigInt = false;
    if (!isFloat && this.charAt(this.pos) === "n") {
      isBigInt = true;
      this.advance();
    }

    const token: Token = {
      kind: "number",
      text: this.source.slice(startOffset, this.pos),
      span: this.span(startOffset, startLine, startCol),
      numeric: { isFloat, isBigInt, base },
    };
    this.push(out, token);
  }

  private lexIdent(out: Token[]): void {
    const startOffset = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    while (isIdentContinue(this.charAt(this.pos))) this.advance();
    const text = this.source.slice(startOffset, this.pos);
    const token: Token = {
      kind: KEYWORDS.has(text) ? "keyword" : "ident",
      text,
      span: this.span(startOffset, startLine, startCol),
    };
    this.push(out, token);
  }

  private lexPunct(out: Token[]): void {
    const startOffset = this.pos;
    const startLine = this.line;
    const startCol = this.col;
    for (const punct of PUNCTUATORS) {
      if (punct === "?." && isDigit(this.charAt(this.pos + 2))) continue; // `x?.5` is `x ? .5 : …`
      if (this.source.startsWith(punct, this.pos)) {
        for (let i = 0; i < punct.length; i += 1) this.advance();
        this.push(out, {
          kind: "punct",
          text: punct,
          span: this.span(startOffset, startLine, startCol),
        });
        return;
      }
    }
    // Anything else (`\`, a lone `?` in weird input, …) becomes a one-character
    // punctuator so that the token stream stays well formed.
    const text = this.advance();
    this.push(out, { kind: "punct", text, span: this.span(startOffset, startLine, startCol) });
  }

  private regexAllowed(): boolean {
    const prev = this.prev;
    if (prev === null) return true;
    switch (prev.kind) {
      case "ident":
      case "number":
      case "string":
      case "template":
      case "regex":
        return false;
      case "keyword":
        return !EXPR_ENDING_KEYWORDS.has(prev.text);
      case "punct":
        return !EXPR_ENDING_PUNCT.has(prev.text);
      default:
        return true;
    }
  }
}

/** Tokenize a whole file.  Never throws; errors come back as diagnostics. */
export function lex(source: string, file: string): LexResult {
  return new Lexer(source, file).run();
}

/** Decode the cooked value of a string token (`"a\nb"` -> `a<newline>b`). */
export function decodeStringLiteral(raw: string): string {
  if (raw.length < 2) return raw;
  const body = raw.slice(1, -1);
  let out = "";
  for (let i = 0; i < body.length; i += 1) {
    const ch = body[i]!;
    if (ch !== "\\") {
      out += ch;
      continue;
    }
    const next = body[i + 1];
    i += 1;
    switch (next) {
      case "n":
        out += "\n";
        break;
      case "t":
        out += "\t";
        break;
      case "r":
        out += "\r";
        break;
      case "b":
        out += "\b";
        break;
      case "f":
        out += "\f";
        break;
      case "v":
        out += "\v";
        break;
      case "0":
        out += "\0";
        break;
      case "\n":
        break; // line continuation
      case "\r":
        if (body[i + 1] === "\n") i += 1;
        break;
      case "x": {
        const hex = body.slice(i + 1, i + 3);
        out += String.fromCharCode(Number.parseInt(hex, 16) || 0);
        i += 2;
        break;
      }
      case "u": {
        if (body[i + 1] === "{") {
          const close = body.indexOf("}", i + 1);
          const hex = close === -1 ? "" : body.slice(i + 2, close);
          out += String.fromCodePoint(Number.parseInt(hex, 16) || 0);
          i = close === -1 ? body.length : close;
        } else {
          const hex = body.slice(i + 1, i + 5);
          out += String.fromCharCode(Number.parseInt(hex, 16) || 0);
          i += 4;
        }
        break;
      }
      case undefined:
        break;
      default:
        out += next;
        break;
    }
  }
  return out;
}

/** Convenience for tests and the parser: the position of a token's first character. */
export function tokenPosition(source: string, token: Token): { line: number; col: number } {
  return offsetToPosition(source, token.span.offset);
}
