# Syntax layer notes (milestone 4)

Untrusted, and pure except for `crosscheck.ts`, the only file touching `Bun.Transpiler`. Nothing here imports `typescript`.

## Entry points

- `src/diagnostics.ts` — `Span { file, line, col, offset, endOffset? }` (1-based line/col, 0-based offsets), `DiagnosticKind`, `Diagnostic { kind, severity, span, message, path?, counterexample? }`, `formatDiagnostic` → `file:line:col: error[post]: message` plus `  path: …` / `  counterexample: …`, `sortDiagnostics`, `spanFromOffsets`, `joinSpans`, `offsetToPosition`, `spanContains`.
- `src/syntax/lexer.ts` — `lex(source, file): { tokens, diagnostics }`; never throws. `Token = { kind: "ident"|"keyword"|"number"|"string"|"template"|"regex"|"punct"|"jsdoc"|"eof", text, span, numeric?, template?, regex? }`; `template` is `{type:"text",raw,span}` / `{type:"expr",tokens,span}` parts and `tokens` ends with an `eof`. Also exported: `decodeStringLiteral`, `isWordToken`, `isPunct`, `isKeyword`.
- `src/syntax/jsdoc.ts` — `parseJSDoc(raw, span): JSDocBlock`; `specTags(block)`, `tagsNamed(block, name)`, `tagSourceOffset(tag, textOffset)`.
- `src/syntax/parser.ts` — `parseFile(path, source, opts?): ParsedFile`, `opts.includeUnannotated`.
- `src/syntax/print.ts` — `printFunction`, `printExpr` (fully parenthesised), `printStmt`, `printBlock`, `printParam`, `printVarDecl`, `printType`.
- `src/syntax/crosscheck.ts` — `sameParse(original, ourPrint)`, `normalizeWithBun`, `crosscheckFunction(fn, source): Diagnostic | null`, `crosscheckFunctions(fns, source)`.

## ParsedFile

`{ path, functions: FnDecl[], typeAliases: TypeAliasDecl[], imports: ImportDecl[], diagnostics }`. Only functions whose JSDoc has `@pre`/`@post`/`@decreases` are fully parsed; **all** `type` aliases and imports are. Every other top-level item is skipped by matching braces at the token level. `diagnostics` are sorted by (file, offset, end, kind, message); `parse` covers lexer errors, JSDoc errors and syntax errors, while `fragment` is only produced by milestone 5.

## Declarations

`FnDecl = { kind:"FnDecl", name, nameSpan, typeParams: {name,span}[], typeParamsText?, params: Param[], returnType?: TypeAnn, returnTypeText?, body: BlockStmt, jsdoc: JSDocBlock|null, exported, async, generator, span, text }`; `text` is the verbatim declaration (no JSDoc).
`Param = { name, nameSpan, typeAnn?, typeText?, optional, rest, defaultText?, span }`; `typeText`/`returnTypeText` are verbatim source slices (the printer copies them).
`TypeAliasDecl = { name, nameSpan, typeParams, variants: Variant[], span, text }` with `Variant = { name: string|null, fields: Field[], discriminant: Discriminant|null, span, text }`, `Field = { name, nameSpan, readonly, typeAnn, typeText, span }`, `Discriminant = { key, value, keySpan, valueSpan }` (cooked string literal).
`ImportDecl = { specifier, specifierSpan, relative, defaultImport, namespaceImport, bindings: {imported, local, typeOnly, span}[], typeOnly, span, text }`.

## Statements (`Stmt`)

`Block{body}`, `VarDecl{declKind:"const"|"let"|"var", declarations:{name,nameSpan,typeAnn?,typeText?,init?,span}[]}`, `ExprStmt{expr}`, `If{test,then,alternate}`, `Return{argument|null}`, `Switch{discriminant,cases:{test|null,body,span,braced}[]}`, `While{test,body,jsdoc}`, `For{init|null,test|null,update|null,body,jsdoc}`, `Throw{argument}`, `Break{label}`, `Continue{label}`, `Empty`, `Unsupported{what,text}`. There is no `do/while`, `for…of/in`, `try`, nested `function`/`class` or labelled-statement node: those become `Unsupported` with verbatim `text` (printed as-is), so milestone 5 reports them as `fragment` at `span`.

## Expressions (`Expr`)

`Lit{lit:"int"|"float"|"string"|"boolean"|"bigint"|"hex"|"regex", raw, value, regex?}`, `Ident{name}`, `This`, `ArrayLit{elements,multiline}`, `ObjectLit{props,multiline}`, `Template{parts}`, `Member{object,property,propertySpan,optional}`, `Index{object,index,optional}`, `Call{callee,args,optional,typeArgsText?}`, `New{callee,args|null}`, `Unary{op,operand}`, `Update{op,operand,prefix}`, `Binary{op,left,right}`, `Logical{op,left,right}`, `Assign{op,target,value}`, `Cond{test,consequent,alternate}`, `Arrow{params,body,typeText?,async}`, `As{expr,typeText}`, `NonNull{expr}`, `Spread{expr}`, `Await{expr}`, `Yield{delegate,argument}`, `Seq{exprs}`, `Unsupported{what,text}`.

For milestone 5 these nodes *are* the rejections: `AnyType`/`UnknownType`, `ArrayType` with `readonly:false`, `BooleanType` (outside conditions), `This`, `As`, `NonNull`, `Arrow`, `New`, `Await`, `Yield`, `Spread` outside an array literal, `Update`/compound `Assign` outside loop updates, `Member`/`Index`/`Call` with `optional:true`, `Binary` with `/ % & | ^ << >> >>> == !=`, `Lit` with `lit:"float"|"bigint"|"regex"`, mutation of a parameter (an `Assign`/`Update` targeting one), and `Unsupported`. Type annotations are `NumberType`, `BooleanType`, `ArrayType{readonly,elem}`, `NameType{name}` (type parameter or union alias, resolved later), `AnyType`, `UnknownType`, `OtherType{text}`; the parser rejects none of them.

## Loop JSDoc

A JSDoc block written directly before a `while`/`for` becomes that loop's `jsdoc`; only spec blocks (`@invariant`/`@decreases`) are reported on, and a loop is the only place they attach. A spec block preceding any other statement is a `parse` diagnostic. A function's `jsdoc` is the preceding block whether or not it has spec tags (prose is allowed). `JSDocTag = { name, text (joined, leading `*` stripped), raw, span, nameSpan, textSpan, isSpec, segments }`; `tagSourceOffset(tag, i)` maps an offset in `tag.text` to a file offset (a joining space maps to the end of the previous line) when parsing a spec expression.

## Cross-check contract

`printFunction(fn)` prints statements in their original form (braces kept, `if`/`else` shape kept) and every expression fully parenthesised, with type annotations copied verbatim; comments and JSDoc are omitted. `sameParse(fn.text, printFunction(fn))` compares `Bun.Transpiler({loader:"ts"}).transformSync` of both. Bun drops redundant parentheses and re-indents, so equal output means an equal parse; `crosscheckFunction` returns an `internal` diagnostic on mismatch. Two Bun quirks the printer reproduces: braced and unbraced `if` bodies normalise differently, and an array/object literal keeps its line structure when its *top level* (before the first item, between items, or before the closing bracket) contains a newline. Type aliases are never cross-checked: Bun normalises them to `""`. Callers should skip the cross-check for functions whose span contains a `parse` diagnostic.
