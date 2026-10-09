/**
 * Printer for the cross-check.
 *
 * Statements are printed in the same *form* they were parsed (braces kept where
 * the source had braces, `if`/`else` chains kept, one line per statement), and
 * every expression is fully parenthesised.  Bun's own printer drops redundant
 * parentheses and re-indents, so `Bun.Transpiler.transformSync` of this output
 * equals that of the original **iff** the parse is structurally right:
 *
 *   printExpr(a - b - c)  =  "(((a) - (b)) - (c))"   -> Bun: a - b - c
 *   printExpr(a - (b - c)) = "((a) - ((b) - (c)))"   -> Bun: a - (b - c)
 *
 * Types are copied verbatim from the original source slice, because Bun strips
 * type annotations from both sides and verbatim text is the safest thing to
 * hand it.  Comments (including JSDoc) are omitted, which Bun also strips.
 *
 * Array and object literals are the one place where Bun preserves the source's
 * line structure, so `printExpr` emits a multi-line layout exactly when the
 * original literal spanned lines (the `multiline` flag).
 */

import type * as A from "./ast";

const INDENT = "  ";

const WORD_UNARY: ReadonlySet<string> = new Set(["typeof", "void", "delete"]);

/** Print a whole function declaration (without its JSDoc). */
export function printFunction(fn: A.FnDecl): string {
  const parts: string[] = [];
  if (fn.exported) parts.push("export");
  if (fn.async) parts.push("async");
  let head = parts.length > 0 ? `${parts.join(" ")} function` : "function";
  if (fn.generator) head += "*";
  head += ` ${fn.name}`;
  head += fn.typeParamsText !== undefined && fn.typeParamsText !== ""
    ? fn.typeParamsText
    : fn.typeParams.length > 0
      ? `<${fn.typeParams.map((p) => p.name).join(", ")}>`
      : "";
  head += `(${fn.params.map(printParam).join(", ")})`;
  if (fn.returnTypeText !== undefined) head += `: ${fn.returnTypeText}`;
  return `${head} ${printBlock(fn.body, 0)}`;
}

export function printParam(param: A.Param): string {
  let out = param.rest ? "..." : "";
  out += param.name;
  if (param.optional) out += "?";
  if (param.typeText !== undefined) out += `: ${param.typeText}`;
  if (param.defaultText !== undefined) out += ` = ${param.defaultText}`;
  return out;
}

/** Print a braced block at `indent` levels of indentation. */
export function printBlock(block: A.BlockStmt, indent: number): string {
  if (block.body.length === 0) return "{}";
  const pad = INDENT.repeat(indent);
  const lines = block.body.map((stmt) => printStmt(stmt, indent + 1));
  return `{\n${lines.join("\n")}\n${pad}}`;
}

/** Print one statement, with its leading indentation. */
export function printStmt(stmt: A.Stmt, indent: number): string {
  const pad = INDENT.repeat(indent);
  switch (stmt.kind) {
    case "Block":
      return pad + printBlock(stmt, indent);
    case "VarDecl":
      return pad + printVarDecl(stmt) + ";";
    case "ExprStmt":
      return pad + printExpr(stmt.expr) + ";";
    case "If": {
      let out = `if (${printExpr(stmt.test)}) ${printStmt(stmt.then, indent).slice(pad.length)}`;
      if (stmt.alternate !== null) {
        out += ` else ${printStmt(stmt.alternate, indent).slice(pad.length)}`;
      }
      return pad + out;
    }
    case "Return":
      return pad + (stmt.argument === null ? "return;" : `return ${printExpr(stmt.argument)};`);
    case "Switch": {
      let out = `switch (${printExpr(stmt.discriminant)}) {`;
      for (const switchCase of stmt.cases) {
        out += `\n${INDENT.repeat(indent + 1)}${switchCase.test === null ? "default:" : `case ${printExpr(switchCase.test)}:`}`;
        for (const inner of switchCase.body) {
          out += `\n${printStmt(inner, indent + 2 + (switchCase.braced ? 1 : 0))}`;
        }
      }
      return pad + out + `\n${pad}}`;
    }
    case "While":
      return pad + `while (${printExpr(stmt.test)}) ${printStmt(stmt.body, indent).slice(pad.length)}`;
    case "For": {
      const init =
        stmt.init === null
          ? ""
          : stmt.init.kind === "VarDecl"
            ? printVarDecl(stmt.init)
            : stmt.init.kind === "ExprStmt"
              ? printExpr(stmt.init.expr)
              : printStmt(stmt.init, 0).trim();
      const test = stmt.test === null ? "" : printExpr(stmt.test);
      const update = stmt.update === null ? "" : printExpr(stmt.update);
      return pad + `for (${init}; ${test}; ${update}) ${printStmt(stmt.body, indent).slice(pad.length)}`;
    }
    case "Throw":
      return pad + `throw ${printExpr(stmt.argument)};`;
    case "Break":
      return pad + (stmt.label === null ? "break;" : `break ${stmt.label};`);
    case "Continue":
      return pad + (stmt.label === null ? "continue;" : `continue ${stmt.label};`);
    case "Empty":
      return pad + ";";
    case "Unsupported":
      return pad + stmt.text;
    default:
      return pad + ";";
  }
}

/** Print a `const`/`let`/`var` declaration without its terminating semicolon. */
export function printVarDecl(stmt: A.VarDeclStmt): string {
  const declarators = stmt.declarations.map((decl) => {
    let out = decl.name;
    if (decl.typeText !== undefined) out += `: ${decl.typeText}`;
    if (decl.init !== undefined) out += ` = ${printExpr(decl.init)}`;
    return out;
  });
  return `${stmt.declKind} ${declarators.join(", ")}`;
}

/** Print an expression fully parenthesised; precedence is expressed by the tree. */
export function printExpr(expr: A.Expr): string {
  switch (expr.kind) {
    case "Lit":
      return expr.raw;
    case "Ident":
      return expr.name;
    case "This":
      return "this";
    case "ArrayLit":
      if (expr.elements.length === 0) return "[]";
      if (!expr.multiline) return `[${expr.elements.map(printExpr).join(", ")}]`;
      return `[\n${expr.elements.map((e) => INDENT + printExpr(e)).join(",\n")}\n]`;
    case "ObjectLit": {
      if (expr.props.length === 0) return "{}";
      const items = expr.props.map(printProp);
      if (!expr.multiline) return `{ ${items.join(", ")} }`;
      return `{\n${items.map((item) => INDENT + item).join(",\n")}\n}`;
    }
    case "Template":
      return `\`${expr.parts
        .map((part) => (part.type === "text" ? part.raw : `\${${printExpr(part.expr)}}`))
        .join("")}\``;
    case "Member":
      return `(${printExpr(expr.object)})${expr.optional ? "?." : "."}${expr.property}`;
    case "Index":
      return `(${printExpr(expr.object)})${expr.optional ? "?.[" : "["}${printExpr(expr.index)}]`;
    case "Call": {
      const typeArgs = expr.typeArgsText === undefined ? "" : expr.typeArgsText;
      return `(${printExpr(expr.callee)})${expr.optional ? "?." : ""}${typeArgs}(${expr.args
        .map(printExpr)
        .join(", ")})`;
    }
    case "New":
      return `new (${printExpr(expr.callee)})${
        expr.args === null ? "" : `(${expr.args.map(printExpr).join(", ")})`
      }`;
    case "Unary":
      return `(${expr.op}${WORD_UNARY.has(expr.op) ? " " : ""}${printExpr(expr.operand)})`;
    case "Update":
      return expr.prefix
        ? `(${expr.op}${printExpr(expr.operand)})`
        : `(${printExpr(expr.operand)}${expr.op})`;
    case "Binary":
    case "Logical":
      return `(${printExpr(expr.left)} ${expr.op} ${printExpr(expr.right)})`;
    case "Assign":
      return `(${printExpr(expr.target)} ${expr.op} ${printExpr(expr.value)})`;
    case "Cond":
      return `(${printExpr(expr.test)} ? ${printExpr(expr.consequent)} : ${printExpr(expr.alternate)})`;
    case "Arrow": {
      const head = `${expr.async ? "async " : ""}(${expr.params.map(printParam).join(", ")})${
        expr.typeText === undefined ? "" : `: ${expr.typeText}`
      }`;
      const body = expr.body.kind === "Block" ? printBlock(expr.body, 1) : printExpr(expr.body);
      return `(${head} => ${body})`;
    }
    case "As":
      return `(${printExpr(expr.expr)} as ${expr.typeText})`;
    case "NonNull":
      return `(${printExpr(expr.expr)}!)`;
    case "Spread":
      return `...${printExpr(expr.expr)}`;
    case "Await":
      return `(await ${printExpr(expr.expr)})`;
    case "Yield":
      return `(yield${expr.delegate ? "*" : ""}${
        expr.argument === null ? "" : ` ${printExpr(expr.argument)}`
      })`;
    case "Seq":
      return `(${expr.exprs.map(printExpr).join(", ")})`;
    case "Unsupported":
      return expr.text;
    default:
      return "";
  }
}

function printProp(prop: A.ObjectProp): string {
  if (prop.kind === "SpreadProp") return `...${printExpr(prop.expr)}`;
  if (prop.shorthand) return printExpr(prop.value);
  const key =
    prop.keyKind === "computed" && prop.computedKey !== undefined
      ? `[${printExpr(prop.computedKey)}]`
      : prop.keyKind === "string"
        ? JSON.stringify(prop.keyText)
        : prop.keyText;
  return `${key}: ${printExpr(prop.value)}`;
}

/** Text of a type annotation: verbatim when we have it, canonical otherwise. */
export function printType(ann: A.TypeAnn | undefined, verbatim?: string): string {
  if (verbatim !== undefined) return verbatim;
  if (ann === undefined) return "";
  switch (ann.kind) {
    case "NumberType":
      return "number";
    case "BooleanType":
      return "boolean";
    case "ArrayType":
      return `${ann.readonly ? "readonly " : ""}${printType(ann.elem)}[]`;
    case "NameType":
      return ann.name;
    case "AnyType":
      return "any";
    case "UnknownType":
      return "unknown";
    case "OtherType":
      return ann.text;
    default:
      return "";
  }
}
