/**
 * AST for the verified fragment — plus, deliberately, a superset grammar.
 *
 * The parser never rejects a construct that section 4.2 lists as rejected; it
 * produces a node with a span so that milestone 5 (`src/extract/fragment.ts`)
 * can report `file:line:col: error[fragment]: …` naming the construct.  Nodes
 * that only exist to be rejected are marked "rejected construct" below.
 *
 * Every node carries a `span`; declaration nodes also carry the verbatim source
 * text so the printer and the cross-check can use it.
 */

import type { Diagnostic, Span } from "../diagnostics";
import type { JSDocBlock } from "./jsdoc";

export interface Node {
  span: Span;
}

// ---------------------------------------------------------------- type syntax

/**
 * Type annotations the parser understands structurally.  `OtherType` is the
 * catch-all and keeps the verbatim text; nothing here is rejected at parse
 * time (milestone 5 does that).
 */
export type TypeAnn =
  | { kind: "NumberType"; span: Span }
  | { kind: "BooleanType"; span: Span }
  /** `readonly T[]` (readonly: true) or `T[]` / `Array<T>` (readonly: false). */
  | { kind: "ArrayType"; readonly: boolean; elem: TypeAnn; span: Span }
  /** A type parameter or a union alias name; resolved later. */
  | { kind: "NameType"; name: string; span: Span }
  /** rejected construct */
  | { kind: "AnyType"; span: Span }
  /** rejected construct */
  | { kind: "UnknownType"; span: Span }
  | { kind: "OtherType"; text: string; span: Span };

export interface TypeParam {
  name: string;
  span: Span;
}

// ------------------------------------------------------------------ expressions

export type LitKind = "int" | "float" | "string" | "boolean" | "bigint" | "hex" | "regex";

export interface Lit extends Node {
  kind: "Lit";
  lit: LitKind;
  /** Verbatim source text (`0xFF`, `1_000n`, `"a\n"`, …). */
  raw: string;
  /** bigint for int/hex/bigint, number for float, string, boolean for booleans. */
  value: bigint | number | string | boolean;
  regex?: { pattern: string; flags: string };
}

export interface Ident extends Node {
  kind: "Ident";
  name: string;
}

/** rejected construct */
export interface ThisExpr extends Node {
  kind: "This";
}

export interface ArrayLit extends Node {
  kind: "ArrayLit";
  /** Elements; `Spread` nodes are `...e` (rejected outside array literals). */
  elements: Expr[];
  /** True when the literal spans several lines in the source (Bun preserves this). */
  multiline: boolean;
}

export type ObjectProp =
  | {
      kind: "Prop";
      keyText: string;
      keyKind: "ident" | "string" | "number" | "computed";
      computedKey?: Expr;
      value: Expr;
      shorthand: boolean;
      span: Span;
    }
  | { kind: "SpreadProp"; expr: Expr; span: Span };

export interface ObjectLit extends Node {
  kind: "ObjectLit";
  props: ObjectProp[];
  multiline: boolean;
}

export type TemplateElement =
  | { type: "text"; raw: string; span: Span }
  | { type: "expr"; expr: Expr; span: Span };

export interface TemplateLit extends Node {
  kind: "Template";
  /** Alternating text and `${ … }` expression elements. */
  parts: TemplateElement[];
}

export interface MemberExpr extends Node {
  kind: "Member";
  object: Expr;
  property: string;
  propertySpan: Span;
  /** `a?.b` (rejected construct when true) */
  optional: boolean;
}

export interface IndexExpr extends Node {
  kind: "Index";
  object: Expr;
  index: Expr;
  /** `a?.[i]` (rejected construct when true) */
  optional: boolean;
}

export interface CallExpr extends Node {
  kind: "Call";
  callee: Expr;
  args: Expr[];
  /** `f?.()` (rejected construct when true) */
  optional: boolean;
  /** Explicit type arguments, verbatim (`f<number>(x)`), when present. */
  typeArgsText?: string;
}

export interface NewExpr extends Node {
  kind: "New";
  callee: Expr;
  /** null for `new C` with no argument list. */
  args: Expr[] | null;
}

export type UnaryOp = "-" | "+" | "!" | "~" | "typeof" | "void" | "delete";

export interface UnaryExpr extends Node {
  kind: "Unary";
  op: UnaryOp;
  operand: Expr;
}

export interface UpdateExpr extends Node {
  kind: "Update";
  op: "++" | "--";
  operand: Expr;
  prefix: boolean;
}

export type BinaryOp =
  | "**"
  | "*"
  | "/"
  | "%"
  | "+"
  | "-"
  | "<<"
  | ">>"
  | ">>>"
  | "<"
  | "<="
  | ">"
  | ">="
  | "instanceof"
  | "in"
  | "=="
  | "!="
  | "==="
  | "!=="
  | "&"
  | "^"
  | "|";

export interface BinaryExpr extends Node {
  kind: "Binary";
  op: BinaryOp;
  left: Expr;
  right: Expr;
}

export interface LogicalExpr extends Node {
  kind: "Logical";
  op: "&&" | "||" | "??";
  left: Expr;
  right: Expr;
}

export type AssignOp =
  | "="
  | "+="
  | "-="
  | "*="
  | "/="
  | "%="
  | "**="
  | "<<="
  | ">>="
  | ">>>="
  | "&="
  | "|="
  | "^="
  | "&&="
  | "||="
  | "??=";

export interface AssignExpr extends Node {
  kind: "Assign";
  op: AssignOp;
  target: Expr;
  value: Expr;
}

export interface CondExpr extends Node {
  kind: "Cond";
  test: Expr;
  consequent: Expr;
  alternate: Expr;
}

/** rejected construct */
export interface ArrowExpr extends Node {
  kind: "Arrow";
  params: Param[];
  body: Expr | BlockStmt;
  typeText?: string;
  async: boolean;
}

/** rejected construct */
export interface AsExpr extends Node {
  kind: "As";
  expr: Expr;
  /** Verbatim type text after `as`. */
  typeText: string;
}

/** rejected construct (`e!`) */
export interface NonNullExpr extends Node {
  kind: "NonNull";
  expr: Expr;
}

/** `...e` in an array literal, call or object literal. */
export interface SpreadExpr extends Node {
  kind: "Spread";
  expr: Expr;
}

/** rejected construct */
export interface AwaitExpr extends Node {
  kind: "Await";
  expr: Expr;
}

/** rejected construct */
export interface YieldExpr extends Node {
  kind: "Yield";
  delegate: boolean;
  argument: Expr | null;
}

/** The comma operator. */
export interface SeqExpr extends Node {
  kind: "Seq";
  exprs: Expr[];
}

/**
 * A construct the parser recognised but does not model structurally (class or
 * function expressions, `import()`, `<T>e` assertions, tagged templates, …).
 * `text` is the verbatim source slice, which is what the printer re-emits.
 */
export interface UnsupportedExpr extends Node {
  kind: "Unsupported";
  what: string;
  text: string;
}

export type Expr =
  | Lit
  | Ident
  | ThisExpr
  | ArrayLit
  | ObjectLit
  | TemplateLit
  | MemberExpr
  | IndexExpr
  | CallExpr
  | NewExpr
  | UnaryExpr
  | UpdateExpr
  | BinaryExpr
  | LogicalExpr
  | AssignExpr
  | CondExpr
  | ArrowExpr
  | AsExpr
  | NonNullExpr
  | SpreadExpr
  | AwaitExpr
  | YieldExpr
  | SeqExpr
  | UnsupportedExpr;

// ------------------------------------------------------------------ statements

export interface Param {
  name: string;
  nameSpan: Span;
  typeAnn?: TypeAnn;
  /** Verbatim annotation text without the leading `:`. */
  typeText?: string;
  optional: boolean;
  rest: boolean;
  /** Verbatim initializer of a default parameter (`x = e`), when present. */
  defaultText?: string;
  span: Span;
}

export interface VarDeclarator {
  name: string;
  nameSpan: Span;
  typeAnn?: TypeAnn;
  typeText?: string;
  init?: Expr;
  span: Span;
}

export interface VarDeclStmt extends Node {
  kind: "VarDecl";
  declKind: "const" | "let" | "var";
  declarations: VarDeclarator[];
}

/** An expression statement; the fragment accepts only the reassignment forms. */
export interface ExprStmt extends Node {
  kind: "ExprStmt";
  expr: Expr;
}

export interface IfStmt extends Node {
  kind: "If";
  test: Expr;
  then: Stmt;
  alternate: Stmt | null;
}

export interface ReturnStmt extends Node {
  kind: "Return";
  argument: Expr | null;
}

export interface SwitchCase {
  /** null for `default`. */
  test: Expr | null;
  body: Stmt[];
  span: Span;
  /** True when this case's statements are written as a braced block. */
  braced: boolean;
}

export interface SwitchStmt extends Node {
  kind: "Switch";
  discriminant: Expr;
  cases: SwitchCase[];
}

export interface WhileStmt extends Node {
  kind: "While";
  test: Expr;
  body: Stmt;
  /** JSDoc block written directly before the loop, if any. */
  jsdoc: JSDocBlock | null;
}

export interface ForStmt extends Node {
  kind: "For";
  init: Stmt | null;
  test: Expr | null;
  update: Expr | null;
  body: Stmt;
  jsdoc: JSDocBlock | null;
}

export interface BlockStmt extends Node {
  kind: "Block";
  body: Stmt[];
}

/** rejected construct */
export interface ThrowStmt extends Node {
  kind: "Throw";
  argument: Expr;
}

export interface BreakStmt extends Node {
  kind: "Break";
  label: string | null;
}

export interface ContinueStmt extends Node {
  kind: "Continue";
  label: string | null;
}

export interface EmptyStmt extends Node {
  kind: "Empty";
}

/** A complete but unmodelled statement (`try`, `do/while`, `for…of`, a nested
 * function declaration, a class, …).  `text` is the verbatim source slice. */
export interface UnsupportedStmt extends Node {
  kind: "Unsupported";
  what: string;
  text: string;
}

export type Stmt =
  | VarDeclStmt
  | ExprStmt
  | IfStmt
  | ReturnStmt
  | SwitchStmt
  | WhileStmt
  | ForStmt
  | BlockStmt
  | ThrowStmt
  | BreakStmt
  | ContinueStmt
  | EmptyStmt
  | UnsupportedStmt;

// ---------------------------------------------------------------- declarations

export interface FnDecl extends Node {
  kind: "FnDecl";
  name: string;
  nameSpan: Span;
  typeParams: TypeParam[];
  /** Verbatim `<…>` text; non-empty with `typeParams` empty for bounded params. */
  typeParamsText?: string;
  params: Param[];
  returnType?: TypeAnn;
  /** Verbatim return annotation text without the leading `:`. */
  returnTypeText?: string;
  body: BlockStmt;
  /** JSDoc block directly before the declaration (may be prose-only). */
  jsdoc: JSDocBlock | null;
  exported: boolean;
  async: boolean;
  generator: boolean;
  /** Verbatim source text of the whole declaration (no JSDoc). */
  text: string;
}

export interface Field {
  name: string;
  nameSpan: Span;
  readonly: boolean;
  typeAnn: TypeAnn;
  /** Verbatim annotation text without the leading `:`. */
  typeText: string;
  span: Span;
}

export interface Discriminant {
  key: string;
  /** Cooked string value of the literal type. */
  value: string;
  keySpan: Span;
  valueSpan: Span;
}

export interface Variant {
  /** Identifier when the variant is written as a named type; null when inline. */
  name: string | null;
  fields: Field[];
  /** The `readonly kind: "square"` field, when the variant has one. */
  discriminant: Discriminant | null;
  span: Span;
  /** Verbatim source text of the variant. */
  text: string;
}

export interface TypeAliasDecl extends Node {
  kind: "TypeAliasDecl";
  name: string;
  nameSpan: Span;
  typeParams: TypeParam[];
  variants: Variant[];
  /** Verbatim source text of the whole alias (including a leading `export`). */
  text: string;
}

export interface ImportBinding {
  imported: string;
  local: string;
  typeOnly: boolean;
  span: Span;
}

export interface ImportDecl extends Node {
  kind: "ImportDecl";
  /** Module specifier as written. */
  specifier: string;
  specifierSpan: Span;
  /** True when the specifier starts with `./` or `../`. */
  relative: boolean;
  defaultImport: { name: string; span: Span } | null;
  namespaceImport: { name: string; span: Span } | null;
  bindings: ImportBinding[];
  typeOnly: boolean;
  /** Verbatim source text of the whole import declaration. */
  text: string;
}

export interface ParsedFile {
  path: string;
  /** Fully parsed functions: those whose JSDoc has a `@pre`/`@post`/`@decreases` tag. */
  functions: FnDecl[];
  typeAliases: TypeAliasDecl[];
  imports: ImportDecl[];
  diagnostics: Diagnostic[];
}
