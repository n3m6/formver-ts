/**
 * Fragment parser: recursive descent with precedence climbing.
 *
 * `parseFile` fully parses only
 *   (a) functions whose JSDoc has at least one `@pre`/`@post`/`@decreases` tag,
 *   (b) all `type` aliases,
 *   (c) all `import` declarations,
 * and skips everything else at the top level by matching braces on tokens.
 *
 * Inside an annotated function the grammar is a *superset* of the verified
 * fragment: constructs section 4.2 rejects are parsed into real nodes (see
 * `ast.ts`) so that milestone 5 can reject each one with a precise, located
 * message.  Syntactic errors (unexpected tokens, unterminated literals) become
 * `parse` diagnostics; parsing recovers at statement boundaries, so one broken
 * statement does not hide the rest.
 */

import {
  type Diagnostic,
  type Span,
  joinSpans,
  sortDiagnostics,
  spanFromOffsets,
} from "../diagnostics";
import type * as A from "./ast";
import { type JSDocBlock, parseJSDoc } from "./jsdoc";
import {
  type Token,
  decodeStringLiteral,
  isPunct,
  isWord,
  isWordToken,
  lex,
} from "./lexer";

export interface ParseOptions {
  /** Also fully parse functions that have no `@pre`/`@post`/`@decreases` tags. */
  includeUnannotated?: boolean;
}

/** Tag names that make a function a verified function (section 4.2). */
const FUNCTION_TAGS: ReadonlySet<string> = new Set(["pre", "post", "decreases"]);

const ASSIGN_OPS: ReadonlySet<string> = new Set([
  "=",
  "+=",
  "-=",
  "*=",
  "/=",
  "%=",
  "**=",
  "<<=",
  ">>=",
  ">>>=",
  "&=",
  "|=",
  "^=",
  "&&=",
  "||=",
  "??=",
]);

const BINARY_PREC: ReadonlyMap<string, number> = new Map([
  ["??", 4],
  ["||", 5],
  ["&&", 6],
  ["|", 7],
  ["^", 8],
  ["&", 9],
  ["==", 10],
  ["!=", 10],
  ["===", 10],
  ["!==", 10],
  ["<", 11],
  ["<=", 11],
  [">", 11],
  [">=", 11],
  ["instanceof", 11],
  ["in", 11],
  ["<<", 12],
  [">>", 12],
  [">>>", 12],
  ["+", 13],
  ["-", 13],
  ["*", 14],
  ["/", 14],
  ["%", 14],
  ["**", 15],
]);

const PREFIX_UNARY: ReadonlySet<string> = new Set(["-", "+", "!", "~"]);

const STATEMENT_KEYWORDS: ReadonlySet<string> = new Set([
  "const",
  "let",
  "var",
  "if",
  "else",
  "return",
  "switch",
  "case",
  "default",
  "while",
  "for",
  "do",
  "throw",
  "break",
  "continue",
  "function",
  "class",
  "try",
  "catch",
  "finally",
  "type",
  "interface",
  "enum",
  "namespace",
  "declare",
  "debugger",
  "import",
  "export",
  "with",
]);

/** Type-annotation scanning context; controls where a verbatim scan stops. */
type TypeContext = "params" | "arrow" | "other";

class ParseFailure extends Error {
  constructor(
    message: string,
    readonly span: Span,
  ) {
    super(message);
  }
}

export function parseFile(path: string, source: string, opts: ParseOptions = {}): A.ParsedFile {
  const lexed = lex(source, path);
  const diagnostics: Diagnostic[] = [...lexed.diagnostics];
  const parser = new Parser(lexed.tokens, source, path, diagnostics, {
    includeUnannotated: opts.includeUnannotated === true,
  });
  const parsed = parser.run();
  return {
    path,
    functions: parsed.functions,
    typeAliases: parsed.typeAliases,
    imports: parsed.imports,
    diagnostics: sortDiagnostics(diagnostics),
  };
}

class Parser {
  private pos = 0;
  private pendingJsDoc: Token | null = null;
  private readonly functions: A.FnDecl[] = [];
  private readonly typeAliases: A.TypeAliasDecl[] = [];
  private readonly imports: A.ImportDecl[] = [];

  constructor(
    private readonly tokens: Token[],
    private readonly source: string,
    private readonly path: string,
    private readonly diagnostics: Diagnostic[],
    private readonly opts: Required<ParseOptions>,
  ) {}

  run(): { functions: A.FnDecl[]; typeAliases: A.TypeAliasDecl[]; imports: A.ImportDecl[] } {
    while (!this.eof()) this.parseTopLevelItem();
    return { functions: this.functions, typeAliases: this.typeAliases, imports: this.imports };
  }

  // ------------------------------------------------------------------- cursor

  private at(index = 0): Token {
    const i = Math.min(this.pos + index, this.tokens.length - 1);
    return this.tokens[i]!;
  }

  private get cur(): Token {
    return this.at(0);
  }

  private prevToken(): Token {
    return this.tokens[Math.max(0, this.pos - 1)]!;
  }

  private eof(): boolean {
    return this.cur.kind === "eof";
  }

  private next(): Token {
    const token = this.cur;
    if (!this.eof()) this.pos += 1;
    return token;
  }

  private isP(text?: string): boolean {
    return isPunct(this.cur, text);
  }

  private isW(text?: string): boolean {
    return isWordToken(this.cur, text);
  }

  private expectPunct(text: string, what = `\`${text}\``): Token {
    if (!this.isP(text)) this.fail(`expected ${what}`);
    return this.next();
  }

  private fail(message: string, span: Span = this.cur.span): never {
    throw new ParseFailure(message, span);
  }

  private error(span: Span, message: string): void {
    this.diagnostics.push({ kind: "parse", severity: "error", span, message });
  }

  private newlineBefore(): boolean {
    const prev = this.prevToken();
    const start = prev.span.endOffset ?? prev.span.offset;
    return this.source.slice(start, this.cur.span.offset).includes("\n");
  }

  private spanBetween(start: Span, end: Span): Span {
    return joinSpans(start, end);
  }

  /** Parse a JSDoc token; its diagnostics are only reported when it is a spec block. */
  private block(token: Token): JSDocBlock {
    return parseJSDoc(token.text, token.span);
  }

  private useBlock(block: JSDocBlock | null): JSDocBlock | null {
    if (block !== null && block.hasSpecTags) this.diagnostics.push(...block.diagnostics);
    return block;
  }

  private isFunctionSpec(block: JSDocBlock | null): boolean {
    return block !== null && block.tags.some((tag) => FUNCTION_TAGS.has(tag.name));
  }

  // ------------------------------------------------------------- top-level pass

  private parseTopLevelItem(): void {
    const before = this.pos;
    const token = this.cur;
    if (token.kind === "jsdoc") {
      this.pendingJsDoc = token;
      this.next();
      return;
    }
    if (this.isP(";")) {
      this.next();
      this.pendingJsDoc = null;
      return;
    }
    let handled = false;
    if (this.tryParseImport()) handled = true;
    else if (this.tryParseTypeAlias()) handled = true;
    else if (this.tryParseFunction()) handled = true;
    if (!handled) this.skipTopLevelStatement();
    this.pendingJsDoc = null;
    // Skipping can stop on a token that cannot start a top-level item (a stray
    // `}` after a construct we mis-stepped over).  Never spin on it.
    if (this.pos === before && !this.eof()) {
      this.error(this.cur.span, `unexpected \`${this.cur.text}\` at the top level`);
      this.next();
    }
  }

  /** Tokens that plausibly begin a new top-level item (used for ASI-style skipping). */
  private startsTopLevelStatement(index: number): boolean {
    const token = this.tokens[index];
    if (token === undefined) return false;
    if (token.kind === "jsdoc") return true;
    if (isWord(token)) return STATEMENT_KEYWORDS.has(token.text);
    return isPunct(token, "@");
  }

  /** Skip one top-level statement that we do not need to parse. */
  private skipTopLevelStatement(): void {
    const start = this.pos;
    let depth = 0;
    while (!this.eof()) {
      const token = this.cur;
      if (token.kind === "jsdoc" && depth === 0 && this.pos > start) return;
      if (isPunct(token, "{") || isPunct(token, "(") || isPunct(token, "[")) {
        depth += 1;
      } else if (isPunct(token, "}") || isPunct(token, ")") || isPunct(token, "]")) {
        if (depth === 0) return;
        depth -= 1;
      } else if (isPunct(token, ";") && depth === 0) {
        this.next();
        return;
      } else if (depth === 0 && this.pos > start && this.newlineBefore() && this.startsTopLevelStatement(this.pos)) {
        return;
      }
      this.next();
    }
    if (this.pos === start && !this.eof()) this.next();
  }

  // -------------------------------------------------------------------- imports

  private tryParseImport(): boolean {
    const start = this.pos;
    if (!this.isW("import")) return false;
    const after = this.at(1);
    if (isPunct(after, "(") || isPunct(after, ".") || isPunct(after, "=")) return false;
    const startToken = this.next();
    let typeOnly = false;
    if (this.isW("type")) {
      const nextToken = this.at(1);
      // `import type { … }`, `import type * as ns`, `import type Def`; but
      // `import type from "./m"` imports a binding called `type`.
      const isTypeOnly =
        isPunct(nextToken, "{") ||
        isPunct(nextToken, "*") ||
        (isWord(nextToken) && !isWordToken(nextToken, "from"));
      if (isTypeOnly) {
        typeOnly = true;
        this.next();
      }
    }
    let defaultImport: A.ImportDecl["defaultImport"] = null;
    let namespaceImport: A.ImportDecl["namespaceImport"] = null;
    const bindings: A.ImportBinding[] = [];
    if (isWord(this.cur) && !this.isW("from")) {
      const name = this.next();
      defaultImport = { name: name.text, span: name.span };
      if (this.isP(",")) this.next();
    }
    if (this.isP("*")) {
      this.next();
      if (!this.isW("as")) {
        this.pos = start;
        return false;
      }
      this.next();
      if (!isWord(this.cur)) {
        this.pos = start;
        return false;
      }
      const name = this.next();
      namespaceImport = { name: name.text, span: name.span };
    } else if (this.isP("{")) {
      this.next();
      while (!this.eof() && !this.isP("}")) {
        let bindingTypeOnly = false;
        if (this.isW("type")) {
          const nextToken = this.at(1);
          if (isWord(nextToken)) {
            bindingTypeOnly = true;
            this.next();
          }
        }
        if (!isWord(this.cur)) {
          this.pos = start;
          return false;
        }
        const imported = this.next();
        let local = imported;
        if (this.isW("as")) {
          this.next();
          if (!isWord(this.cur)) {
            this.pos = start;
            return false;
          }
          local = this.next();
        }
        bindings.push({
          imported: imported.text,
          local: local.text,
          typeOnly: bindingTypeOnly,
          span: this.spanBetween(imported.span, local.span),
        });
        if (this.isP(",")) this.next();
        else break;
      }
      if (!this.isP("}")) {
        this.pos = start;
        return false;
      }
      this.next();
    }
    if (this.isW("from")) {
      this.next();
    } else if (defaultImport !== null || namespaceImport !== null || bindings.length > 0) {
      this.pos = start;
      return false;
    }
    if (this.cur.kind !== "string") {
      this.pos = start;
      return false;
    }
    const specifier = this.next();
    this.consumeSemicolon();
    const end = this.prevToken();
    this.imports.push({
      kind: "ImportDecl",
      specifier: decodeStringLiteral(specifier.text),
      specifierSpan: specifier.span,
      relative: specifier.text.startsWith('"./') || specifier.text.startsWith('"../') ||
        specifier.text.startsWith("'./") || specifier.text.startsWith("'../"),
      defaultImport,
      namespaceImport,
      bindings,
      typeOnly,
      span: this.spanBetween(startToken.span, end.span),
      text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
    });
    return true;
  }

  // --------------------------------------------------------------- type aliases

  private tryParseTypeAlias(): boolean {
    const start = this.pos;
    try {
      return this.tryParseTypeAliasInner();
    } catch (error) {
      if (!(error instanceof ParseFailure)) throw error;
      this.pos = start;
      this.skipTopLevelStatement();
      return true;
    }
  }

  private tryParseTypeAliasInner(): boolean {
    const start = this.pos;
    let startToken = this.cur;
    if (this.isW("export")) {
      const after = this.at(1);
      if (!isWordToken(after, "type")) return false;
      startToken = this.next();
    }
    if (!this.isW("type")) {
      this.pos = start;
      return false;
    }
    const nameToken = this.at(1);
    const afterName = this.at(2);
    if (!isWord(nameToken) || !(isPunct(afterName, "=") || isPunct(afterName, "<"))) {
      this.pos = start;
      return false;
    }
    this.next(); // `type`
    const name = this.next();
    const typeParams = this.parseTypeParams();
    const variants: A.Variant[] = [];
    if (this.isP("=")) {
      this.next();
      this.parseUnionVariants(variants);
    }
    this.consumeSemicolon();
    const end = this.prevToken();
    this.typeAliases.push({
      kind: "TypeAliasDecl",
      name: name.text,
      nameSpan: name.span,
      typeParams,
      variants,
      span: this.spanBetween(startToken.span, end.span),
      text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
    });
    return true;
  }

  private parseUnionVariants(out: A.Variant[]): void {
    for (;;) {
      if (this.isP("|")) {
        this.next();
        continue;
      }
      if (this.eof() || this.isP(";")) return;
      const startToken = this.cur;
      if (this.isP("{")) {
        out.push(this.parseObjectVariant());
      } else {
        // Any other member (`Other`, `"square"`, `Record<string, unknown>`, …) is
        // kept verbatim; milestone 5 rejects a variant that is not a tagged
        // object type.
        const memberStart = this.pos;
        let depth = 0;
        let count = 0;
        while (!this.eof()) {
          const token = this.cur;
          if (token.kind === "jsdoc") break;
          if (isPunct(token, "{") || isPunct(token, "(") || isPunct(token, "[")) {
            depth += 1;
          } else if (isPunct(token, "}") || isPunct(token, ")") || isPunct(token, "]")) {
            if (depth === 0) break;
            depth -= 1;
          } else if (depth === 0 && (isPunct(token, "|") || isPunct(token, ";"))) {
            break;
          } else if (depth === 0 && count > 0 && this.newlineBefore() && this.startsTopLevelStatement(this.pos)) {
            break;
          }
          this.next();
          count += 1;
        }
        if (count === 0) {
          this.error(this.cur.span, "unsupported type alias member");
          this.next();
          continue;
        }
        const end = this.prevToken();
        const single = count === 1 && this.tokens[memberStart]!.kind === "ident";
        out.push({
          name: single ? this.tokens[memberStart]!.text : null,
          fields: [],
          discriminant: null,
          span: this.spanBetween(startToken.span, end.span),
          text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
        });
      }
      if (this.isP("|")) continue;
      if (this.isP(",")) {
        this.next();
        continue;
      }
      if (this.eof() || this.isP(";")) return;
      if (this.isP("&")) {
        this.error(this.cur.span, "intersection types are not supported in a verified type alias");
        this.next();
        continue;
      }
      if (this.newlineBefore() && this.startsTopLevelStatement(this.pos)) return;
      this.error(this.cur.span, "expected `|` between union variants");
      return;
    }
  }

  private parseObjectVariant(): A.Variant {
    const open = this.expectPunct("{");
    const fields: A.Field[] = [];
    while (!this.eof() && !this.isP("}")) {
      if (this.isP(";") || this.isP(",")) {
        this.next();
        continue;
      }
      const fieldStart = this.cur;
      let readonly = false;
      if (this.isW("readonly")) {
        readonly = true;
        this.next();
      }
      if (!isWord(this.cur)) {
        this.error(this.cur.span, "unsupported type alias member");
        while (!this.eof() && !this.isP(";") && !this.isP(",") && !this.isP("}")) this.next();
        continue;
      }
      const name = this.next();
      if (this.isP("?")) this.next();
      if (!this.isP(":")) {
        this.error(this.cur.span, `expected \`:\` after field \`${name.text}\``);
        while (!this.eof() && !this.isP(";") && !this.isP(",") && !this.isP("}")) this.next();
        continue;
      }
      this.next();
      const [typeAnn, typeText] = this.parseTypeAnnotation("other");
      const end = this.prevToken();
      fields.push({
        name: name.text,
        nameSpan: name.span,
        readonly,
        typeAnn,
        typeText,
        span: this.spanBetween(fieldStart.span, end.span),
      });
      if (this.isP(";") || this.isP(",")) this.next();
    }
    const close = this.expectPunct("}");
    const text = this.source.slice(open.span.offset, close.span.endOffset ?? close.span.offset);
    return {
      name: null,
      fields,
      discriminant: findDiscriminant(fields),
      span: this.spanBetween(open.span, close.span),
      text,
    };
  }

  // ------------------------------------------------------------------ functions

  private tryParseFunction(): boolean {
    const start = this.pos;
    try {
      return this.tryParseFunctionInner();
    } catch (error) {
      if (!(error instanceof ParseFailure)) throw error;
      // A failure while reading the signature (params, return type, type
      // parameters) escapes the statement-level recovery.  Report it only when
      // the declaration is one we were asked to verify, then skip it whole.
      this.pos = start;
      const block = this.pendingJsDoc === null ? null : this.block(this.pendingJsDoc);
      if (this.isFunctionSpec(block)) {
        this.useBlock(block);
        this.error(error.span, error.message);
      }
      this.skipTopLevelStatement();
      return true;
    }
  }

  private tryParseFunctionInner(): boolean {
    const start = this.pos;
    let startToken = this.cur;
    let exported = false;
    if (this.isW("export")) {
      const after = this.at(1);
      if (isWordToken(after, "default")) {
        startToken = this.next();
        this.next();
        exported = true;
      } else if (isWordToken(after, "async") || isWordToken(after, "function")) {
        startToken = this.next();
        exported = true;
      } else {
        return false;
      }
    }
    let async = false;
    if (this.isW("async")) {
      if (!isWordToken(this.at(1), "function")) {
        this.pos = start;
        return false;
      }
      this.next();
      async = true;
    }
    if (!this.isW("function")) {
      this.pos = start;
      return false;
    }
    this.next();
    let generator = false;
    if (this.isP("*")) {
      generator = true;
      this.next();
    }
    if (!isWord(this.cur) || this.cur.kind !== "ident") {
      this.pos = start;
      return false;
    }
    const name = this.next();
    const typeParamsStart = this.cur.span.offset;
    const typeParams = this.parseTypeParams();
    const typeParamsText = this.source.slice(typeParamsStart, this.prevToken().span.endOffset ?? typeParamsStart);
    const params = this.parseParams();
    let returnType: A.TypeAnn | undefined;
    let returnTypeText: string | undefined;
    if (this.isP(":")) {
      const typeStart = this.at(1).span.offset;
      this.next();
      [returnType, returnTypeText] = this.parseTypeAnnotation("other");
      // A return type we do not model but that keeps going (`value is T`,
      // `asserts x is T`, …): keep the text verbatim so the body still parses.
      if (!this.isP("{") && !this.isP(";") && !this.eof()) {
        let depth = 0;
        while (!this.eof()) {
          const token = this.cur;
          if (token.kind === "jsdoc") break;
          if (isPunct(token, "(") || isPunct(token, "[") || isPunct(token, "{")) {
            if (isPunct(token, "{") && depth === 0) break;
            depth += 1;
          } else if (isPunct(token, ")") || isPunct(token, "]") || isPunct(token, "}")) {
            if (depth === 0) break;
            depth -= 1;
          } else if (depth === 0 && isPunct(token, ";")) {
            break;
          }
          this.next();
        }
        const end = this.prevToken().span.endOffset ?? typeStart;
        const text = this.source.slice(typeStart, Math.max(typeStart, end));
        returnType = {
          kind: "OtherType",
          text,
          span: spanFromOffsets(this.path, this.source, typeStart, Math.max(typeStart, end)),
        };
        returnTypeText = text;
      }
    }
    if (!this.isP("{")) {
      // An overload signature: skip it, there is no body to verify.
      while (!this.eof() && !this.isP(";")) this.next();
      if (this.isP(";")) this.next();
      return true;
    }

    const pendingToken = this.pendingJsDoc;
    const block = pendingToken === null ? null : this.block(pendingToken);
    const annotated = this.isFunctionSpec(block);
    if (!annotated && !this.opts.includeUnannotated) {
      this.skipBalancedBlock();
      return true;
    }
    this.useBlock(block);
    const body = this.parseBlock();
    const end = this.prevToken();
    this.functions.push({
      kind: "FnDecl",
      name: name.text,
      nameSpan: name.span,
      typeParams,
      typeParamsText,
      params,
      returnType,
      returnTypeText,
      body,
      jsdoc: block,
      exported,
      async,
      generator,
      span: this.spanBetween(startToken.span, end.span),
      text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
    });
    return true;
  }

  /** Skip `{ … }` starting at the current token. */
  private skipBalancedBlock(): void {
    this.expectPunct("{");
    let depth = 1;
    while (!this.eof() && depth > 0) {
      if (this.isP("{")) depth += 1;
      else if (this.isP("}")) depth -= 1;
      this.next();
    }
  }

  private parseTypeParams(): A.TypeParam[] {
    const params: A.TypeParam[] = [];
    if (!this.isP("<")) return params;
    const start = this.pos;
    this.next();
    while (!this.eof() && !this.isP(">")) {
      if (isWord(this.cur) && this.cur.kind === "ident") {
        const name = this.next();
        params.push({ name: name.text, span: name.span });
        if (this.isW("extends")) {
          // Bounded type parameter: outside the fragment, but parse it so the
          // caller can reject it.  Roll back and treat the whole `<…>` as opaque.
          this.pos = start;
          this.skipBalancedAngles();
          return [];
        }
      } else {
        this.pos = start;
        this.skipBalancedAngles();
        return [];
      }
      if (this.isP(",")) this.next();
      else break;
    }
    if (!this.isP(">")) {
      this.pos = start;
      this.skipBalancedAngles();
      return [];
    }
    this.next();
    return params;
  }

  private skipBalancedAngles(): void {
    if (!this.isP("<")) return;
    let depth = 0;
    while (!this.eof()) {
      if (this.isP("<")) depth += 1;
      else if (this.isP(">")) depth -= 1;
      else if (this.isP(">>") || this.isP(">>>")) depth -= this.cur.text.length;
      else if (isPunct(this.cur, ";") || isPunct(this.cur, "{") || isPunct(this.cur, "(")) return;
      this.next();
      if (depth <= 0) return;
    }
  }

  private parseParams(): A.Param[] {
    const params: A.Param[] = [];
    this.expectPunct("(");
    while (!this.eof() && !this.isP(")")) {
      const startToken = this.cur;
      let rest = false;
      if (this.isP("...")) {
        rest = true;
        this.next();
      }
      if (!isWord(this.cur) || this.cur.kind !== "ident") {
        if (this.isP("{") || this.isP("[")) this.fail("destructuring parameters are not supported");
        this.fail("expected a parameter name");
      }
      const name = this.next();
      let optional = false;
      if (this.isP("?")) {
        optional = true;
        this.next();
      }
      let typeAnn: A.TypeAnn | undefined;
      let typeText: string | undefined;
      if (this.isP(":")) {
        this.next();
        [typeAnn, typeText] = this.parseTypeAnnotation("params");
      }
      let defaultText: string | undefined;
      if (this.isP("=")) {
        this.next();
        const value = this.parseAssignment();
        defaultText = this.source.slice(
          value.span.offset,
          value.span.endOffset ?? value.span.offset,
        );
      }
      const end = this.prevToken();
      params.push({
        name: name.text,
        nameSpan: name.span,
        typeAnn,
        typeText,
        optional,
        rest,
        defaultText,
        span: this.spanBetween(startToken.span, end.span),
      });
      if (this.isP(",")) this.next();
      else break;
    }
    if (!this.isP(")")) this.fail("expected `)` to close the parameter list");
    this.next();
    return params;
  }

  // ----------------------------------------------------------------- statements

  private parseBlock(): A.BlockStmt {
    const open = this.expectPunct("{");
    const body: A.Stmt[] = [];
    let pending: JSDocBlock | null = null;
    while (!this.eof() && !this.isP("}")) {
      if (this.cur.kind === "jsdoc") {
        pending = this.block(this.cur);
        this.next();
        continue;
      }
      const before = this.pos;
      try {
        body.push(this.parseStatement(pending));
        pending = null;
      } catch (error) {
        if (!(error instanceof ParseFailure)) throw error;
        this.error(error.span, error.message);
        this.synchronize();
        pending = null;
      }
      if (this.pos === before) this.next();
    }
    if (!this.isP("}")) {
      this.error(this.cur.span, "unterminated block: expected `}`");
    } else {
      this.next();
    }
    return { kind: "Block", body, span: this.spanBetween(open.span, this.prevToken().span) };
  }

  /** Skip to a statement boundary after a parse error. */
  private synchronize(): void {
    let depth = 0;
    const start = this.pos;
    while (!this.eof()) {
      const token = this.cur;
      if (token.kind === "jsdoc" && depth === 0 && this.pos > start) return;
      if (isPunct(token, "{") || isPunct(token, "(") || isPunct(token, "[")) {
        depth += 1;
      } else if (isPunct(token, "}") || isPunct(token, ")") || isPunct(token, "]")) {
        if (depth === 0) return;
        depth -= 1;
      } else if (isPunct(token, ";") && depth === 0) {
        this.next();
        return;
      } else if (depth === 0 && this.pos > start && isWord(token) && STATEMENT_KEYWORDS.has(token.text)) {
        return;
      }
      this.next();
    }
  }

  private parseStatement(pendingIn: JSDocBlock | null): A.Stmt {
    let pending = pendingIn;
    while (this.cur.kind === "jsdoc") {
      pending = this.block(this.cur);
      this.next();
    }
    const statement = this.parseStatementInner(pending);
    if (pending !== null && pending.hasSpecTags && statement.kind !== "While" && statement.kind !== "For") {
      this.error(
        pending.span,
        "`@invariant`/`@decreases` must annotate a `while` or `for` loop",
      );
    }
    return statement;
  }

  private parseStatementInner(pending: JSDocBlock | null): A.Stmt {
    const token = this.cur;
    if (isPunct(token, "{")) return this.parseBlock();
    if (isPunct(token, ";")) {
      this.next();
      return { kind: "Empty", span: token.span };
    }
    if (isWord(token)) {
      switch (token.text) {
        case "const":
        case "let":
        case "var":
          if (token.text === "let" && !this.startsDeclaration()) break;
          return this.parseVarDeclStatement();
        case "if":
          return this.parseIf();
        case "return":
          return this.parseReturn();
        case "switch":
          return this.parseSwitch();
        case "while":
          return this.parseWhile(pending);
        case "for":
          return this.parseFor(pending);
        case "throw": {
          const start = this.next();
          const argument = this.parseExpression();
          this.consumeSemicolon();
          return {
            kind: "Throw",
            argument,
            span: this.spanBetween(start.span, this.prevToken().span),
          };
        }
        case "break":
        case "continue": {
          const start = this.next();
          let label: string | null = null;
          if (isWord(this.cur) && this.cur.kind === "ident" && !this.newlineBefore()) {
            label = this.next().text;
          }
          this.consumeSemicolon();
          const span = this.spanBetween(start.span, this.prevToken().span);
          return start.text === "break"
            ? { kind: "Break", label, span }
            : { kind: "Continue", label, span };
        }
        case "function":
          return this.parseUnsupported("nested function declaration");
        case "class":
          return this.parseUnsupported("class declaration");
        case "try":
          return this.parseUnsupported("`try` statement");
        case "do":
          this.next();
          this.skipUnsupportedStatement();
          this.skipDoWhileTail();
          return {
            kind: "Unsupported",
            what: "`do`/`while` statement",
            text: this.source.slice(
              token.span.offset,
              this.prevToken().span.endOffset ?? token.span.offset,
            ),
            span: this.spanBetween(token.span, this.prevToken().span),
          };
        case "with":
          return this.parseUnsupported("`with` statement");
        case "debugger":
          return this.parseUnsupported("`debugger` statement");
        case "import":
          return this.parseUnsupported("`import` inside a function");
        case "export":
          return this.parseUnsupported("`export` inside a function");
        case "interface":
        case "enum":
        case "namespace":
        case "declare":
        case "abstract":
          if (isWord(this.at(1)) && this.at(1).kind === "ident") {
            return this.parseUnsupported(`${token.text} declaration`);
          }
          break;
        case "async":
          if (isWordToken(this.at(1), "function")) {
            return this.parseUnsupported("nested function declaration");
          }
          break;
        case "type":
          if (
            isWord(this.at(1)) &&
            this.at(1).kind === "ident" &&
            (isPunct(this.at(2), "=") || isPunct(this.at(2), "<"))
          ) {
            return this.parseUnsupported("type alias inside a function");
          }
          break;
        default:
          break;
      }
    }
    // A labelled statement: `label: …`.
    if (isWord(token) && this.cur.kind === "ident" && isPunct(this.at(1), ":")) {
      return this.parseUnsupported("labelled statement");
    }
    return this.parseExprStatement();
  }

  private startsDeclaration(): boolean {
    const after = this.at(1);
    if (isWord(after) && after.kind === "ident") return true;
    return isPunct(after, "{") || isPunct(after, "[");
  }

  private parseVarDeclStatement(consumeSemi = true): A.VarDeclStmt {
    const keyword = this.next();
    const declKind = keyword.text as "const" | "let" | "var";
    const declarations: A.VarDeclarator[] = [];
    for (;;) {
      const startToken = this.cur;
      if (isPunct(this.cur, "{") || isPunct(this.cur, "[")) {
        this.fail("destructuring declarations are not supported");
      }
      if (!isWord(this.cur) || this.cur.kind !== "ident") this.fail("expected a variable name");
      const name = this.next();
      let typeAnn: A.TypeAnn | undefined;
      let typeText: string | undefined;
      if (this.isP(":")) {
        this.next();
        [typeAnn, typeText] = this.parseTypeAnnotation("other");
      }
      let init: A.Expr | undefined;
      if (this.isP("=")) {
        this.next();
        init = this.parseAssignment();
      }
      declarations.push({
        name: name.text,
        nameSpan: name.span,
        typeAnn,
        typeText,
        init,
        span: this.spanBetween(startToken.span, this.prevToken().span),
      });
      if (this.isP(",")) {
        this.next();
        continue;
      }
      break;
    }
    if (consumeSemi) this.consumeSemicolon();
    return {
      kind: "VarDecl",
      declKind,
      declarations,
      span: this.spanBetween(keyword.span, this.prevToken().span),
    };
  }

  private parseIf(): A.IfStmt {
    const start = this.next();
    this.expectPunct("(");
    const test = this.parseExpression();
    this.expectPunct(")");
    const then = this.parseStatement(null);
    let alternate: A.Stmt | null = null;
    if (this.isW("else")) {
      this.next();
      alternate = this.parseStatement(null);
    }
    return {
      kind: "If",
      test,
      then,
      alternate,
      span: this.spanBetween(start.span, (alternate ?? then).span),
    };
  }

  private parseReturn(): A.ReturnStmt {
    const start = this.next();
    let argument: A.Expr | null = null;
    if (!this.isP(";") && !this.isP("}") && !this.eof() && !this.newlineBefore()) {
      argument = this.parseExpression();
    }
    this.consumeSemicolon();
    return {
      kind: "Return",
      argument,
      span: this.spanBetween(start.span, this.prevToken().span),
    };
  }

  private parseSwitch(): A.SwitchStmt {
    const start = this.next();
    this.expectPunct("(");
    const discriminant = this.parseExpression();
    this.expectPunct(")");
    this.expectPunct("{");
    const cases: A.SwitchCase[] = [];
    while (!this.eof() && !this.isP("}")) {
      const caseToken = this.cur;
      if (!this.isW("case") && !this.isW("default")) {
        this.error(this.cur.span, "expected `case` or `default` in a switch");
        this.synchronize();
        continue;
      }
      this.next();
      let test: A.Expr | null = null;
      if (caseToken.text === "case") test = this.parseExpression();
      this.expectPunct(":");
      const body: A.Stmt[] = [];
      let braced = false;
      if (this.isP("{")) {
        body.push(this.parseBlock());
        braced = true;
      } else {
        let pending: JSDocBlock | null = null;
        while (!this.eof() && !this.isP("}") && !this.isW("case") && !this.isW("default")) {
          if (this.cur.kind === "jsdoc") {
            pending = this.block(this.cur);
            this.next();
            continue;
          }
          const before = this.pos;
          body.push(this.parseStatement(pending));
          pending = null;
          if (this.pos === before) this.next();
        }
      }
      cases.push({
        test,
        body,
        braced,
        span: this.spanBetween(caseToken.span, this.prevToken().span),
      });
    }
    this.expectPunct("}");
    return {
      kind: "Switch",
      discriminant,
      cases,
      span: this.spanBetween(start.span, this.prevToken().span),
    };
  }

  private parseWhile(pending: JSDocBlock | null): A.WhileStmt {
    const start = this.next();
    this.expectPunct("(");
    const test = this.parseExpression();
    this.expectPunct(")");
    const body = this.parseStatement(null);
    return {
      kind: "While",
      test,
      body,
      jsdoc: this.attachLoopDoc(pending),
      span: this.spanBetween(start.span, body.span),
    };
  }

  private parseFor(pending: JSDocBlock | null): A.Stmt {
    // `for (… of …)` / `for (… in …)` are outside the fragment; skip them whole.
    if (this.isForEachHeader()) return this.parseUnsupported("`for`…`of`/`in` statement");
    const start = this.next();
    if (!this.isP("(")) this.fail("expected `(` after `for`");
    this.next(); // `(`
    let init: A.Stmt | null = null;
    if (!this.isP(";")) {
      if (this.isW("const") || this.isW("let") || this.isW("var")) {
        init = this.parseVarDeclStatement(false);
      } else {
        const exprStart = this.cur;
        const expr = this.parseExpression();
        init = {
          kind: "ExprStmt",
          expr,
          span: this.spanBetween(exprStart.span, expr.span),
        };
      }
    }
    if (!this.isP(";")) this.fail("expected `;` in the `for` header");
    this.next();
    let test: A.Expr | null = null;
    if (!this.isP(";")) test = this.parseExpression();
    if (!this.isP(";")) this.fail("expected `;` in the `for` header");
    this.next();
    let update: A.Expr | null = null;
    if (!this.isP(")")) update = this.parseExpression();
    this.expectPunct(")");
    const body = this.parseStatement(null);
    return {
      kind: "For",
      init,
      test,
      update,
      body,
      jsdoc: this.attachLoopDoc(pending),
      span: this.spanBetween(start.span, body.span),
    };
  }

  /** With the cursor on `(`, does this look like a `for…of` / `for…in` header? */
  private isForEachHeader(): boolean {
    let depth = 0;
    for (let i = this.pos; i < this.tokens.length; i += 1) {
      const token = this.tokens[i]!;
      if (token.kind === "eof") return false;
      if (isPunct(token, "(") || isPunct(token, "[") || isPunct(token, "{")) {
        depth += 1;
      } else if (isPunct(token, ")") || isPunct(token, "]") || isPunct(token, "}")) {
        depth -= 1;
        if (depth === 0) return false;
      } else if (depth === 1 && (isWordToken(token, "of") || isWordToken(token, "in"))) {
        return true;
      } else if (depth === 1 && isPunct(token, ";")) {
        return false;
      }
    }
    return false;
  }

  /** After a `do` body, consume the trailing `while ( … ) ;`. */
  private skipDoWhileTail(): void {
    if (!this.isW("while")) return;
    this.next();
    if (this.isP("(")) {
      let depth = 0;
      while (!this.eof()) {
        if (this.isP("(")) depth += 1;
        else if (this.isP(")")) {
          depth -= 1;
          this.next();
          if (depth === 0) break;
          continue;
        }
        this.next();
      }
    }
    this.consumeSemicolon();
  }

  /** Attach a JSDoc block to a loop, reporting its diagnostics when it is a spec block. */
  private attachLoopDoc(pending: JSDocBlock | null): JSDocBlock | null {
    if (pending === null) return null;
    if (!pending.hasSpecTags) return null;
    this.diagnostics.push(...pending.diagnostics);
    return pending;
  }

  private parseExprStatement(): A.ExprStmt {
    const expr = this.parseExpression();
    this.consumeSemicolon();
    return {
      kind: "ExprStmt",
      expr,
      span: this.spanBetween(expr.span, this.prevToken().span),
    };
  }

  /** A statement the parser recognised but does not model; text is verbatim. */
  private parseUnsupported(what: string): A.UnsupportedStmt {
    const startToken = this.cur;
    this.skipUnsupportedStatement();
    const end = this.prevToken();
    return {
      kind: "Unsupported",
      what,
      text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
      span: this.spanBetween(startToken.span, end.span),
    };
  }

  private skipUnsupportedStatement(): void {
    const start = this.pos;
    let depth = 0;
    while (!this.eof()) {
      const token = this.cur;
      if (isPunct(token, "{") || isPunct(token, "(") || isPunct(token, "[")) {
        depth += 1;
      } else if (isPunct(token, "}") || isPunct(token, ")") || isPunct(token, "]")) {
        if (depth === 0) return;
        depth -= 1;
      } else if (isPunct(token, ";") && depth === 0) {
        this.next();
        return;
      } else if (depth === 0 && this.pos > start && isWord(token) && STATEMENT_KEYWORDS.has(token.text)) {
        // `catch` / `finally` / `else` continue the construct we are skipping.
        if (token.text === "catch" || token.text === "finally" || token.text === "else") {
          this.next();
          continue;
        }
        return;
      }
      this.next();
    }
  }

  private consumeSemicolon(): void {
    if (this.isP(";")) {
      this.next();
      return;
    }
    if (this.eof() || this.isP("}") || this.newlineBefore()) return;
    this.fail("expected `;`");
  }

  // ---------------------------------------------------------------- expressions

  private parseExpression(): A.Expr {
    const first = this.parseAssignment();
    if (!this.isP(",")) return first;
    const exprs = [first];
    while (this.isP(",")) {
      this.next();
      exprs.push(this.parseAssignment());
    }
    return {
      kind: "Seq",
      exprs,
      span: this.spanBetween(first.span, exprs[exprs.length - 1]!.span),
    };
  }

  private parseAssignment(): A.Expr {
    const left = this.parseConditional();
    const token = this.cur;
    if (token.kind === "punct" && ASSIGN_OPS.has(token.text)) {
      this.next();
      const value = this.parseAssignment();
      return {
        kind: "Assign",
        op: token.text as A.AssignOp,
        target: left,
        value,
        span: this.spanBetween(left.span, value.span),
      };
    }
    return left;
  }

  private parseConditional(): A.Expr {
    const test = this.parseBinary(0);
    if (!this.isP("?")) return test;
    this.next();
    const consequent = this.parseAssignment();
    this.expectPunct(":", "`:` in a conditional expression");
    const alternate = this.parseAssignment();
    return {
      kind: "Cond",
      test,
      consequent,
      alternate,
      span: this.spanBetween(test.span, alternate.span),
    };
  }

  private parseBinary(minPrec: number): A.Expr {
    let left = this.parseUnary();
    for (;;) {
      const token = this.cur;
      if (isWordToken(token, "as")) {
        if (11 < minPrec) break;
        this.next();
        const [, typeText] = this.parseTypeAnnotation("other");
        left = {
          kind: "As",
          expr: left,
          typeText,
          span: this.spanBetween(left.span, this.prevToken().span),
        };
        continue;
      }
      const op = this.binaryOpOf(token);
      if (op === null) break;
      const prec = BINARY_PREC.get(op)!;
      if (prec < minPrec) break;
      this.next();
      const right = this.parseBinary(op === "**" ? prec : prec + 1);
      const span = this.spanBetween(left.span, right.span);
      left =
        op === "&&" || op === "||" || op === "??"
          ? { kind: "Logical", op: op as "&&" | "||" | "??", left, right, span }
          : { kind: "Binary", op: op as A.BinaryOp, left, right, span };
    }
    return left;
  }

  private binaryOpOf(token: Token): string | null {
    if (token.kind === "punct" && BINARY_PREC.has(token.text)) return token.text;
    if (token.kind === "keyword" && (token.text === "instanceof" || token.text === "in")) return token.text;
    return null;
  }

  private parseUnary(): A.Expr {
    const token = this.cur;
    if (token.kind === "punct" && PREFIX_UNARY.has(token.text)) {
      this.next();
      const operand = this.parseUnary();
      return {
        kind: "Unary",
        op: token.text as A.UnaryOp,
        operand,
        span: this.spanBetween(token.span, operand.span),
      };
    }
    if (token.kind === "punct" && (token.text === "++" || token.text === "--")) {
      this.next();
      const operand = this.parseUnary();
      return {
        kind: "Update",
        op: token.text,
        operand,
        prefix: true,
        span: this.spanBetween(token.span, operand.span),
      };
    }
    if (token.kind === "keyword" && (token.text === "typeof" || token.text === "void" || token.text === "delete")) {
      this.next();
      const operand = this.parseUnary();
      return {
        kind: "Unary",
        op: token.text,
        operand,
        span: this.spanBetween(token.span, operand.span),
      };
    }
    if (token.kind === "keyword" && token.text === "await") {
      this.next();
      const operand = this.parseUnary();
      return { kind: "Await", expr: operand, span: this.spanBetween(token.span, operand.span) };
    }
    if (token.kind === "keyword" && token.text === "yield") {
      this.next();
      let delegate = false;
      if (this.isP("*")) {
        delegate = true;
        this.next();
      }
      const argument =
        this.isP(")") || this.isP("]") || this.isP("}") || this.isP(";") || this.isP(",") || this.eof()
          ? null
          : this.parseAssignment();
      return {
        kind: "Yield",
        delegate,
        argument,
        span: this.spanBetween(token.span, (argument ?? token).span),
      };
    }
    if (isPunct(token, "<") && this.looksLikeTypeAssertion()) {
      return this.parseUnsupportedExpr("type assertion");
    }
    return this.parsePostfix();
  }

  private looksLikeTypeAssertion(): boolean {
    // `<T>e` in a `.ts` file.  Distinguish from `a < b` using the previous token.
    const prev = this.prevToken();
    if (isWord(prev) || isPunct(prev, ")") || isPunct(prev, "]")) return false;
    return true;
  }

  private parsePostfix(): A.Expr {
    let expr = this.parseCallMember();
    for (;;) {
      const token = this.cur;
      if ((isPunct(token, "++") || isPunct(token, "--")) && !this.newlineBefore()) {
        this.next();
        expr = {
          kind: "Update",
          op: token.text as "++" | "--",
          operand: expr,
          prefix: false,
          span: this.spanBetween(expr.span, token.span),
        };
        continue;
      }
      break;
    }
    return expr;
  }

  private parseCallMember(): A.Expr {
    let expr = this.isW("new") ? this.parseNew() : this.parsePrimary();
    for (;;) {
      const token = this.cur;
      if (isPunct(token, ".")) {
        this.next();
        if (!isWord(this.cur)) this.fail("expected a property name after `.`");
        const property = this.next();
        expr = {
          kind: "Member",
          object: expr,
          property: property.text,
          propertySpan: property.span,
          optional: false,
          span: this.spanBetween(expr.span, property.span),
        };
        continue;
      }
      if (isPunct(token, "?.")) {
        this.next();
        if (this.isP("(")) {
          const [args, close] = this.parseArguments();
          expr = {
            kind: "Call",
            callee: expr,
            args,
            optional: true,
            span: this.spanBetween(expr.span, close.span),
          };
          continue;
        }
        if (this.isP("[")) {
          this.next();
          const index = this.parseExpression();
          const close = this.expectPunct("]");
          expr = {
            kind: "Index",
            object: expr,
            index,
            optional: true,
            span: this.spanBetween(expr.span, close.span),
          };
          continue;
        }
        if (!isWord(this.cur)) this.fail("expected a property name after `?.`");
        const property = this.next();
        expr = {
          kind: "Member",
          object: expr,
          property: property.text,
          propertySpan: property.span,
          optional: true,
          span: this.spanBetween(expr.span, property.span),
        };
        continue;
      }
      if (isPunct(token, "[")) {
        this.next();
        const index = this.parseExpression();
        const close = this.expectPunct("]");
        expr = {
          kind: "Index",
          object: expr,
          index,
          optional: false,
          span: this.spanBetween(expr.span, close.span),
        };
        continue;
      }
      if (isPunct(token, "(")) {
        const [args, close] = this.parseArguments();
        expr = {
          kind: "Call",
          callee: expr,
          args,
          optional: false,
          span: this.spanBetween(expr.span, close.span),
        };
        continue;
      }
      if (isPunct(token, "!")) {
        this.next();
        expr = { kind: "NonNull", expr, span: this.spanBetween(expr.span, token.span) };
        continue;
      }
      if (token.kind === "template") {
        const template = this.next();
        expr = {
          kind: "Unsupported",
          what: "tagged template",
          text: this.source.slice(expr.span.offset, template.span.endOffset ?? template.span.offset),
          span: this.spanBetween(expr.span, template.span),
        };
        continue;
      }
      if (isPunct(token, "<")) {
        const save = this.pos;
        const typeArgs = this.tryTypeArguments();
        if (typeArgs !== null && this.isP("(")) {
          const [args, close] = this.parseArguments();
          expr = {
            kind: "Call",
            callee: expr,
            args,
            optional: false,
            typeArgsText: typeArgs,
            span: this.spanBetween(expr.span, close.span),
          };
          continue;
        }
        this.pos = save;
      }
      break;
    }
    return expr;
  }

  /** `<T, U>` immediately before a `(`.  Consumes it and returns the verbatim text. */
  private tryTypeArguments(): string | null {
    const startOffset = this.cur.span.offset;
    let depth = 0;
    let i = this.pos;
    while (i < this.tokens.length) {
      const token = this.tokens[i]!;
      if (token.kind === "eof" || token.kind === "jsdoc") return null;
      if (isPunct(token, "<")) {
        depth += 1;
      } else if (isPunct(token, ">")) {
        depth -= 1;
        if (depth === 0) {
          i += 1;
          break;
        }
      } else if (isPunct(token, ">>") || isPunct(token, ">>>")) {
        depth -= token.text.length;
        if (depth <= 0) {
          i += 1;
          break;
        }
      } else if (isPunct(token, ";") || isPunct(token, "{") || isPunct(token, "}") || isPunct(token, "=")) {
        return null;
      }
      i += 1;
    }
    if (depth !== 0) return null;
    const close = this.tokens[i - 1];
    if (close === undefined || !isPunct(this.tokens[i]!, "(")) return null;
    const text = this.source.slice(startOffset, close.span.endOffset ?? close.span.offset);
    this.pos = i;
    return text;
  }

  private parseNew(): A.Expr {
    const start = this.next(); // `new`
    if (this.isP(".")) {
      return this.parseUnsupportedExpr("`new.target`");
    }
    const callee = this.parseNewCallee();
    let args: A.Expr[] | null = null;
    let end: Token = this.prevToken();
    if (this.isP("(")) {
      const [parsed, close] = this.parseArguments();
      args = parsed;
      end = close;
    }
    return {
      kind: "New",
      callee,
      args,
      span: this.spanBetween(start.span, end.span),
    };
  }

  private parseNewCallee(): A.Expr {
    let expr = this.isW("new") ? this.parseNew() : this.parsePrimary();
    for (;;) {
      if (this.isP(".")) {
        this.next();
        if (!isWord(this.cur)) this.fail("expected a property name after `.`");
        const property = this.next();
        expr = {
          kind: "Member",
          object: expr,
          property: property.text,
          propertySpan: property.span,
          optional: false,
          span: this.spanBetween(expr.span, property.span),
        };
        continue;
      }
      if (this.isP("[")) {
        this.next();
        const index = this.parseExpression();
        const close = this.expectPunct("]");
        expr = {
          kind: "Index",
          object: expr,
          index,
          optional: false,
          span: this.spanBetween(expr.span, close.span),
        };
        continue;
      }
      break;
    }
    return expr;
  }

  private parseArguments(): [A.Expr[], Token] {
    this.expectPunct("(");
    const args: A.Expr[] = [];
    while (!this.eof() && !this.isP(")")) {
      if (this.isP("...")) {
        const spread = this.next();
        const value = this.parseAssignment();
        args.push({ kind: "Spread", expr: value, span: this.spanBetween(spread.span, value.span) });
      } else {
        args.push(this.parseAssignment());
      }
      if (this.isP(",")) this.next();
      else break;
    }
    const close = this.expectPunct(")");
    return [args, close];
  }

  private parsePrimary(): A.Expr {
    const token = this.cur;
    switch (token.kind) {
      case "number":
        return this.parseNumberLiteral(token);
      case "string":
        this.next();
        return {
          kind: "Lit",
          lit: "string",
          raw: token.text,
          value: decodeStringLiteral(token.text),
          span: token.span,
        };
      case "template":
        return this.parseTemplateLiteral(this.next());
      case "regex":
        this.next();
        return {
          kind: "Lit",
          lit: "regex",
          raw: token.text,
          value: token.text,
          regex: token.regex,
          span: token.span,
        };
      case "ident": {
        if (token.text === "async") {
          const arrow = this.tryParseAsyncArrow();
          if (arrow !== null) return arrow;
        }
        this.next();
        if (this.isP("=>")) {
          this.next();
          const body = this.isP("{") ? this.parseBlock() : this.parseAssignment();
          const param: A.Param = {
            name: token.text,
            nameSpan: token.span,
            optional: false,
            rest: false,
            span: token.span,
          };
          return {
            kind: "Arrow",
            params: [param],
            body,
            async: false,
            span: this.spanBetween(token.span, body.span),
          };
        }
        return { kind: "Ident", name: token.text, span: token.span };
      }
      case "keyword": {
        switch (token.text) {
          case "this":
            this.next();
            return { kind: "This", span: token.span };
          case "true":
          case "false":
            this.next();
            return {
              kind: "Lit",
              lit: "boolean",
              raw: token.text,
              value: token.text === "true",
              span: token.span,
            };
          case "null":
          case "super":
            this.next();
            return { kind: "Ident", name: token.text, span: token.span };
          case "function":
            return this.parseUnsupportedExpr("function expression");
          case "class":
            return this.parseUnsupportedExpr("class expression");
          case "import":
            return this.parseUnsupportedExpr("dynamic `import`");
          case "new":
            return this.parseNew();
          case "await": {
            this.next();
            const operand = this.parseUnary();
            return { kind: "Await", expr: operand, span: this.spanBetween(token.span, operand.span) };
          }
          default:
            this.fail(`unexpected keyword \`${token.text}\``);
        }
        break;
      }
      case "punct": {
        switch (token.text) {
          case "(":
            return this.parseParenOrArrow();
          case "[":
            return this.parseArrayLiteral();
          case "{":
            return this.parseObjectLiteral();
          case "<":
            return this.parseUnsupportedExpr("type assertion");
          case "@":
            return this.parseUnsupportedExpr("decorator");
          default:
            this.fail(`unexpected token \`${token.text}\``);
        }
        break;
      }
      default:
        break;
    }
    this.fail(this.eof() ? "unexpected end of file" : `unexpected token \`${token.text}\``);
  }

  private parseNumberLiteral(token: Token): A.Lit {
    this.next();
    const info = token.numeric!;
    let lit: A.LitKind;
    let value: bigint | number;
    const digits = token.text.replace(/_/g, "");
    if (info.isFloat) {
      lit = "float";
      value = Number(digits);
    } else if (info.isBigInt) {
      lit = "bigint";
      value = BigInt(digits.slice(0, -1));
    } else if (info.base === "hex") {
      lit = "hex";
      value = BigInt(digits);
    } else if (info.base === "binary") {
      lit = "int";
      value = BigInt(digits);
    } else if (info.base === "octal") {
      lit = "int";
      value = BigInt(digits);
    } else {
      lit = "int";
      value = BigInt(digits);
    }
    return { kind: "Lit", lit, raw: token.text, value, span: token.span };
  }

  private parseTemplateLiteral(token: Token): A.TemplateLit {
    const parts: A.TemplateElement[] = [];
    for (const part of token.template ?? []) {
      if (part.type === "text") {
        parts.push({ type: "text", raw: part.raw, span: part.span });
      } else {
        const sub = new Parser(part.tokens, this.source, this.path, this.diagnostics, this.opts);
        const expr = sub.parseExpression();
        if (!sub.eof()) {
          this.error(sub.cur.span, "unexpected token in a template expression");
        }
        parts.push({ type: "expr", expr, span: part.span });
      }
    }
    return { kind: "Template", parts, span: token.span };
  }

  private parseArrayLiteral(): A.ArrayLit {
    const open = this.expectPunct("[");
    const elements: A.Expr[] = [];
    while (!this.eof() && !this.isP("]")) {
      if (this.isP(",")) {
        // Array elision: `[1, , 2]`.
        elements.push({ kind: "Unsupported", what: "array elision", text: "", span: this.cur.span });
        this.next();
        continue;
      }
      if (this.isP("...")) {
        const spread = this.next();
        const value = this.parseAssignment();
        elements.push({ kind: "Spread", expr: value, span: this.spanBetween(spread.span, value.span) });
      } else {
        elements.push(this.parseAssignment());
      }
      if (this.isP(",")) this.next();
      else break;
    }
    const close = this.expectPunct("]");
    return {
      kind: "ArrayLit",
      elements,
      multiline: this.literalIsMultiline(open, close, elements),
      span: this.spanBetween(open.span, close.span),
    };
  }

  private parseObjectLiteral(): A.ObjectLit {
    const open = this.expectPunct("{");
    const props: A.ObjectProp[] = [];
    while (!this.eof() && !this.isP("}")) {
      if (this.isP("...")) {
        const spread = this.next();
        const value = this.parseAssignment();
        props.push({ kind: "SpreadProp", expr: value, span: this.spanBetween(spread.span, value.span) });
      } else {
        const keyToken = this.cur;
        let keyText: string;
        let keyKind: "ident" | "string" | "number" | "computed";
        let computedKey: A.Expr | undefined;
        if (isPunct(keyToken, "[")) {
          this.next();
          computedKey = this.parseExpression();
          const close = this.expectPunct("]");
          keyKind = "computed";
          keyText = this.source.slice(keyToken.span.offset, close.span.endOffset ?? close.span.offset);
        } else if (keyToken.kind === "string") {
          this.next();
          keyKind = "string";
          keyText = decodeStringLiteral(keyToken.text);
        } else if (keyToken.kind === "number") {
          this.next();
          keyKind = "number";
          keyText = keyToken.text;
        } else if (isWord(keyToken)) {
          this.next();
          keyKind = "ident";
          keyText = keyToken.text;
        } else {
          this.fail("expected an object property name");
        }
        let value: A.Expr;
        let shorthand = false;
        if (this.isP(":")) {
          this.next();
          value = this.parseAssignment();
        } else {
          if (keyKind !== "ident") this.fail("expected `:` after an object property key");
          if (this.isP("(")) this.fail("object methods are not supported");
          shorthand = true;
          value = { kind: "Ident", name: keyText, span: keyToken.span };
        }
        props.push({
          kind: "Prop",
          keyText,
          keyKind,
          computedKey,
          value,
          shorthand,
          span: this.spanBetween(keyToken.span, value.span),
        });
      }
      if (this.isP(",")) this.next();
      else break;
    }
    const close = this.expectPunct("}");
    return {
      kind: "ObjectLit",
      props,
      multiline: this.literalIsMultiline(open, close, props),
      span: this.spanBetween(open.span, close.span),
    };
  }

  /**
   * Bun's printer keeps a literal on one line unless the *top level* of the
   * literal spans lines: a newline before the first item, between two items, or
   * before the closing bracket.  Newlines nested inside an item do not count.
   */
  private literalIsMultiline(
    open: Token,
    close: Token,
    items: ReadonlyArray<{ span: Span }>,
  ): boolean {
    if (items.length === 0) return false;
    let previousEnd = open.span.endOffset ?? open.span.offset;
    for (const item of items) {
      if (this.source.slice(previousEnd, item.span.offset).includes("\n")) return true;
      previousEnd = item.span.endOffset ?? item.span.offset;
    }
    return this.source.slice(previousEnd, close.span.offset).includes("\n");
  }

  private parseParenOrArrow(): A.Expr {
    const start = this.pos;
    const arrow = this.tryParseArrow(false);
    if (arrow !== null) return arrow;
    this.pos = start;
    this.expectPunct("(");
    if (this.isP(")")) this.fail("expected an expression inside parentheses");
    const expr = this.parseExpression();
    this.expectPunct(")");
    return expr;
  }

  private tryParseAsyncArrow(): A.Expr | null {
    const save = this.pos;
    const asyncToken = this.next();
    if (isWord(this.cur) && this.cur.kind === "ident" && isPunct(this.at(1), "=>")) {
      const name = this.next();
      this.next(); // =>
      const body = this.isP("{") ? this.parseBlock() : this.parseAssignment();
      const param: A.Param = {
        name: name.text,
        nameSpan: name.span,
        optional: false,
        rest: false,
        span: name.span,
      };
      return {
        kind: "Arrow",
        params: [param],
        body,
        async: true,
        span: this.spanBetween(asyncToken.span, body.span),
      };
    }
    this.pos = save;
    if (!this.isP("(")) return null;
    const arrow = this.tryParseArrow(true);
    this.pos = save;
    return arrow;
  }

  private tryParseArrow(async: boolean): A.Expr | null {
    const save = this.pos;
    try {
      const startToken = async ? this.tokens[this.pos - 1]! : this.cur;
      const params = this.parseParams();
      let typeText: string | undefined;
      if (this.isP(":")) {
        this.next();
        const [, text] = this.parseTypeAnnotation("arrow");
        typeText = text;
      }
      if (!this.isP("=>")) {
        this.pos = save;
        return null;
      }
      this.next();
      const body: A.Expr | A.BlockStmt = this.isP("{") ? this.parseBlock() : this.parseAssignment();
      return {
        kind: "Arrow",
        params,
        body,
        typeText,
        async,
        span: this.spanBetween(startToken.span, body.span),
      };
    } catch (error) {
      if (error instanceof ParseFailure) {
        this.pos = save;
        return null;
      }
      throw error;
    }
  }

  private parseUnsupportedExpr(what: string): A.UnsupportedExpr {
    const startToken = this.cur;
    if (isPunct(startToken, "<")) {
      // `<T>e` type assertion: skip the type arguments then one unary expression.
      this.skipBalancedAngles();
      const value = this.parseUnary();
      return {
        kind: "Unsupported",
        what,
        text: this.source.slice(startToken.span.offset, value.span.endOffset ?? value.span.offset),
        span: this.spanBetween(startToken.span, value.span),
      };
    }
    if (isWordToken(startToken, "function")) {
      this.next();
      if (this.isP("*")) this.next();
      if (isWord(this.cur) && this.cur.kind === "ident") this.next();
      if (this.isP("<")) this.skipBalancedAngles();
      this.parseParams();
      if (this.isP(":")) {
        this.next();
        this.parseTypeAnnotation("other");
      }
      if (this.isP("{")) this.skipBalancedBlock();
      const end = this.prevToken();
      return {
        kind: "Unsupported",
        what,
        text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
        span: this.spanBetween(startToken.span, end.span),
      };
    }
    if (isWordToken(startToken, "class")) {
      this.next();
      if (isWord(this.cur) && this.cur.kind === "ident") this.next();
      if (this.isP("<")) this.skipBalancedAngles();
      if (this.isW("extends")) {
        this.next();
        this.parseCallMember();
      }
      if (this.isP("{")) this.skipBalancedBlock();
      const end = this.prevToken();
      return {
        kind: "Unsupported",
        what,
        text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
        span: this.spanBetween(startToken.span, end.span),
      };
    }
    if (isWordToken(startToken, "import")) {
      this.next();
      if (this.isP("(")) {
        this.next();
        const args: A.Expr[] = [];
        while (!this.eof() && !this.isP(")")) {
          args.push(this.parseAssignment());
          if (this.isP(",")) this.next();
          else break;
        }
        const close = this.expectPunct(")");
        return {
          kind: "Unsupported",
          what,
          text: this.source.slice(startToken.span.offset, close.span.endOffset ?? close.span.offset),
          span: this.spanBetween(startToken.span, close.span),
        };
      }
    }
    if (isPunct(startToken, "@")) {
      this.next();
      this.parseCallMember();
      const end = this.prevToken();
      return {
        kind: "Unsupported",
        what,
        text: this.source.slice(startToken.span.offset, end.span.endOffset ?? end.span.offset),
        span: this.spanBetween(startToken.span, end.span),
      };
    }
    if (isWordToken(startToken, "new")) {
      const expr = this.parseNew();
      return {
        kind: "Unsupported",
        what,
        text: this.source.slice(startToken.span.offset, expr.span.endOffset ?? expr.span.offset),
        span: expr.span,
      };
    }
    this.fail(`unsupported construct: ${what}`);
  }

  // ------------------------------------------------------------ type annotations

  private parseTypeAnnotation(context: TypeContext): [A.TypeAnn, string] {
    const startOffset = this.cur.span.offset;
    const ann = this.parseTypeAnnotationInner(context);
    const end = this.prevToken().span.endOffset ?? startOffset;
    return [ann, this.source.slice(startOffset, Math.max(startOffset, end))];
  }

  private parseTypeAnnotationInner(context: TypeContext): A.TypeAnn {
    const startPos = this.pos;
    const startSpan = this.cur.span;
    const startOffset = this.cur.span.offset;
    let readonlyPrefix = false;
    if (isWordToken(this.cur, "readonly")) {
      readonlyPrefix = true;
      this.next();
    }
    const atom = this.parseTypeAtom(context, startPos, startOffset);
    let result: A.TypeAnn = atom;
    for (;;) {
      if (!this.isP("[")) break;
      const save = this.pos;
      this.next();
      if (this.isP("]")) {
        this.next();
        result = {
          kind: "ArrayType",
          readonly: readonlyPrefix,
          elem: result,
          span: this.spanBetween(startSpan, this.prevToken().span),
        };
        readonlyPrefix = false;
        continue;
      }
      this.pos = save;
      break;
    }
    // `readonly Foo`, `A | B` and `A & B` are outside the modelled type AST; keep
    // their verbatim text rather than losing the parser's place in a declaration.
    if (readonlyPrefix || this.isP("|") || this.isP("&")) {
      this.pos = startPos;
      return this.parseOtherType(context, startOffset);
    }
    return result;
  }

  private parseTypeAtom(context: TypeContext, startPos: number, startOffset: number): A.TypeAnn {
    const token = this.cur;
    if (isWord(token) && token.kind === "ident") {
      switch (token.text) {
        case "number":
          this.next();
          return { kind: "NumberType", span: token.span };
        case "boolean":
          this.next();
          return { kind: "BooleanType", span: token.span };
        case "any":
          this.next();
          return { kind: "AnyType", span: token.span };
        case "unknown":
          this.next();
          return { kind: "UnknownType", span: token.span };
        case "Array":
        case "ReadonlyArray":
          if (isPunct(this.at(1), "<")) {
            const nameToken = this.next();
            this.next(); // `<`
            const elem = this.parseTypeAnnotationInner(context);
            if (!this.isP(">")) this.fail("expected `>` in a generic type annotation");
            const close = this.next();
            return {
              kind: "ArrayType",
              readonly: nameToken.text === "ReadonlyArray",
              elem,
              span: this.spanBetween(nameToken.span, close.span),
            };
          }
          break;
        default:
          break;
      }
      if (isPunct(this.at(1), "<") || isPunct(this.at(1), ".")) {
        this.pos = startPos;
        return this.parseOtherType(context, startOffset);
      }
      this.next();
      return { kind: "NameType", name: token.text, span: token.span };
    }
    if (isPunct(token, "(")) {
      // Could be a parenthesised type; only a verbatim scan is safe.
      return this.parseOtherType(context, startOffset);
    }
    return this.parseOtherType(context, startOffset);
  }

  /**
   * Scan a type we do not model and keep its verbatim text.  Depth tracking over
   * `<`, `(`, `[` and `{` means nested generics, object types and function types
   * stay in one piece; the scan stops at a top-level `,`, `;`, `=`, `)`, `]`,
   * `}`, `{` (after the first token) or `=>` (in an arrow-return context).
   */
  private parseOtherType(context: TypeContext, startOffset: number): A.TypeAnn {
    let depth = 0;
    let count = 0;
    while (!this.eof()) {
      const token = this.cur;
      if (token.kind === "jsdoc" || token.kind === "eof") break;
      if (token.kind === "punct") {
        const text = token.text;
        if (text === "{") {
          // A `{` starts an object type only at the beginning of a type (or
          // after `|`, `&`, `:`, `,`, `<`, `(`); otherwise it opens the body of
          // the declaration whose return type we are scanning.
          if (depth === 0 && count > 0 && !this.typeContinuesBefore()) break;
          depth += 1;
          this.next();
          count += 1;
          continue;
        }
        if (text === "<" || text === "(" || text === "[") {
          depth += 1;
          this.next();
          count += 1;
          continue;
        }
        if (text === ">" || text === ")" || text === "]" || text === "}") {
          if (depth === 0) break;
          depth -= 1;
          this.next();
          count += 1;
          continue;
        }
        if (depth === 0) {
          if (text === "," || text === ";" || text === "=") break;
          if (text === "=>") {
            if (context === "arrow" && count > 0) break;
            this.next();
            count += 1;
            continue;
          }
        }
      }
      this.next();
      count += 1;
    }
    const end = this.prevToken().span.endOffset ?? startOffset;
    const span = spanFromOffsets(this.path, this.source, startOffset, Math.max(startOffset, end));
    return { kind: "OtherType", text: this.source.slice(startOffset, Math.max(startOffset, end)), span };
  }

  /** True when the previous token can be followed by an object type. */
  private typeContinuesBefore(): boolean {
    const prev = this.prevToken();
    if (prev.kind !== "punct") return false;
    return (
      prev.text === "|" ||
      prev.text === "&" ||
      prev.text === ":" ||
      prev.text === "," ||
      prev.text === "<" ||
      prev.text === "(" ||
      prev.text === "=" ||
      prev.text === "=>"
    );
  }
}

/** The string-literal discriminant of a union variant, if it has one. */
function findDiscriminant(fields: readonly A.Field[]): A.Discriminant | null {
  for (const field of fields) {
    if (field.typeAnn.kind !== "OtherType") continue;
    const text = field.typeAnn.text.trim();
    if (text.length >= 2 && (text.startsWith('"') || text.startsWith("'"))) {
      const last = text[text.length - 1];
      if (last === text[0]) {
        return {
          key: field.name,
          value: decodeStringLiteral(text),
          keySpan: field.nameSpan,
          valueSpan: field.typeAnn.span,
        };
      }
    }
  }
  return null;
}
