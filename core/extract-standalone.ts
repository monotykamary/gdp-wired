// The opt-in scalar reader's closed binding boundary. No module code is run here.
import ts from 'typescript'
import {type Setup, refuse, unparen} from './extract-read.ts'

type Binding = {decl: ts.FunctionDeclaration | ts.VariableDeclaration, order: number}
const reserved = (name: string) => ['undefined', '__cov', '$join', 'this'].includes(name) || name.startsWith('__gdp')

export function standaloneClosure(s: Setup, entry: ts.FunctionLikeDeclaration): string[] {
  const bindings = new Map<ts.Symbol, Binding>(), active = new Set<ts.Node>(), done = new Set<ts.Node>(), reached = new Set<string>()
  const symbol = (id: ts.Identifier): ts.Symbol => s.checker.getSymbolAtLocation(id) ?? refuse(id, 'standalone: unresolved binding')
  const add = (id: ts.Identifier, decl: Binding['decl'], order: number) => {
    if (reserved(id.text)) refuse(id, ts.isFunctionDeclaration(decl) ? 'standalone: reserved function name' : 'standalone: reserved module binding')
    const sym = symbol(id)
    if (bindings.has(sym)) refuse(id, 'standalone: duplicate module binding')
    bindings.set(sym, {decl, order})
  }
  // Declarations of functions and types do not run their bodies on module load. Only
  // inert const initializers may accompany them. Value imports and re-exports can run
  // another module and are deliberately not this frontend's boundary.
  for (const [order, st] of s.sf.statements.entries()) {
    if (ts.isInterfaceDeclaration(st) || ts.isTypeAliasDeclaration(st) || ts.isEmptyStatement(st)) continue
    if (ts.isImportDeclaration(st)) {
      const c = st.importClause
      if (c?.isTypeOnly || (c && !c.name && c.namedBindings && ts.isNamedImports(c.namedBindings) && c.namedBindings.elements.length > 0 && c.namedBindings.elements.every(x => x.isTypeOnly))) continue
      refuse(st, 'standalone: only erased type imports are supported')
    }
    if (ts.isFunctionDeclaration(st) && st.name) { add(st.name, st, order); continue }
    if (ts.isFunctionDeclaration(st) && st === entry) continue
    if (ts.isVariableStatement(st) && st.declarationList.flags & ts.NodeFlags.Const) {
      for (const d of st.declarationList.declarations) {
        if (!ts.isIdentifier(d.name) || !d.initializer) refuse(d, 'standalone: module constants need a simple binding and initializer')
        add(d.name as ts.Identifier, d, order)
      }
      continue
    }
    refuse(st, 'standalone: executable module statement or unsupported declaration')
  }
  const functionOf = (b: Binding): ts.FunctionLikeDeclaration | undefined => {
    if (ts.isFunctionDeclaration(b.decl)) return b.decl
    const e = b.decl.initializer && unparen(b.decl.initializer)
    return e && (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) ? e : undefined
  }
  const inert = (raw: ts.Expression, before: Binding): void => {
    const e = unparen(raw)
    if (ts.isAsExpression(e) || ts.isTypeAssertionExpression(e) || ts.isSatisfiesExpression(e)) { inert(e.expression, before); return }
    if (ts.isNumericLiteral(e)) { if (!Number.isSafeInteger(Number(e.text))) refuse(e, 'standalone: constants must be safe integers'); return }
    if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e) || [ts.SyntaxKind.TrueKeyword, ts.SyntaxKind.FalseKeyword, ts.SyntaxKind.NullKeyword].includes(e.kind)) return
    if (ts.isIdentifier(e)) {
      if (e.text === 'undefined' && !s.checker.getSymbolAtLocation(e)?.valueDeclaration) return
      const b = bindings.get(symbol(e))
      if (!b || b.order >= before.order || functionOf(b)) refuse(e, 'standalone: constant initializer must reference an earlier inert constant')
      return
    }
    if (ts.isArrayLiteralExpression(e)) { for (const x of e.elements) { if (ts.isSpreadElement(x) || ts.isOmittedExpression(x)) refuse(x, 'standalone: array initializer spread or hole'); inert(x as ts.Expression, before) }; return }
    if (ts.isPrefixUnaryExpression(e) && [ts.SyntaxKind.PlusToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.ExclamationToken].includes(e.operator)) { inert(e.operand, before); return }
    refuse(e, 'standalone: module initializer is not inert')
  }
  for (const b of bindings.values()) if (ts.isVariableDeclaration(b.decl) && !functionOf(b)) inert(b.decl.initializer!, b)

  const constant = (b: Binding, at: ts.Node): void => {
    if (active.has(b.decl)) refuse(at, 'standalone: recursive constant')
    if (done.has(b.decl)) return
    if (!ts.isVariableDeclaration(b.decl)) refuse(at, 'standalone: function used as a value')
    active.add(b.decl)
    expression((b.decl as ts.VariableDeclaration).initializer!, new Set())
    active.delete(b.decl); done.add(b.decl); reached.add(b.decl.name!.getText())
  }
  const expression = (raw: ts.Expression, locals: Set<ts.Symbol>): void => {
    const e = unparen(raw)
    if (ts.isAsExpression(e) || ts.isTypeAssertionExpression(e) || ts.isSatisfiesExpression(e)) { expression(e.expression, locals); return }
    if (ts.isNumericLiteral(e) || e.kind === ts.SyntaxKind.TrueKeyword || e.kind === ts.SyntaxKind.FalseKeyword) return
    if (ts.isIdentifier(e)) {
      const sym = s.checker.getSymbolAtLocation(e)
      if (e.text === 'undefined' && !sym?.valueDeclaration) return
      if (sym && locals.has(sym)) return
      const b = sym && bindings.get(sym)
      if (!b) refuse(e, 'standalone: non-input identifier or captured binding')
      if (functionOf(b!)) refuse(e, 'standalone: non-input identifier (function used as a value)')
      constant(b!, e); return
    }
    if (ts.isCallExpression(e)) {
      if (e.questionDotToken || !ts.isIdentifier(e.expression)) refuse(e, 'standalone: only direct closed helper calls are supported')
      const b = bindings.get(symbol(e.expression as ts.Identifier)), fn = b && functionOf(b)
      if (!fn || locals.has(symbol(e.expression as ts.Identifier))) refuse(e, 'standalone: call is not a closed helper')
      if (e.arguments.length !== fn!.parameters.length) refuse(e, 'standalone: helper arguments must match its parameters')
      for (const x of e.arguments) expression(x, locals)
      functionBody(fn!); return
    }
    if (ts.isPrefixUnaryExpression(e) && [ts.SyntaxKind.PlusToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.ExclamationToken].includes(e.operator)) { expression(e.operand, locals); return }
    if (ts.isBinaryExpression(e) && [ts.SyntaxKind.PlusToken, ts.SyntaxKind.MinusToken, ts.SyntaxKind.AsteriskToken, ts.SyntaxKind.PercentToken, ts.SyntaxKind.SlashToken, ts.SyntaxKind.LessThanToken, ts.SyntaxKind.LessThanEqualsToken, ts.SyntaxKind.GreaterThanToken, ts.SyntaxKind.GreaterThanEqualsToken, ts.SyntaxKind.EqualsEqualsToken, ts.SyntaxKind.EqualsEqualsEqualsToken, ts.SyntaxKind.ExclamationEqualsToken, ts.SyntaxKind.ExclamationEqualsEqualsToken, ts.SyntaxKind.AmpersandAmpersandToken, ts.SyntaxKind.BarBarToken, ts.SyntaxKind.QuestionQuestionToken].includes(e.operatorToken.kind)) { expression(e.left, locals); expression(e.right, locals); return }
    if (ts.isConditionalExpression(e)) { expression(e.condition, locals); expression(e.whenTrue, locals); expression(e.whenFalse, locals); return }
    if (ts.isNonNullExpression(e)) { expression(e.expression, locals); return }
    refuse(e, 'standalone: effects or unsupported expression')
  }
  const statement = (st: ts.Statement, locals: Set<ts.Symbol>): void => {
    if (ts.isBlock(st)) { st.statements.forEach(x => statement(x, locals)); return }
    if (ts.isReturnStatement(st)) { if (st.expression) expression(st.expression, locals); return }
    if (ts.isIfStatement(st)) { expression(st.expression, locals); statement(st.thenStatement, locals); if (st.elseStatement) statement(st.elseStatement, locals); return }
    if (ts.isSwitchStatement(st)) {
      expression(st.expression, locals)
      for (const c of st.caseBlock.clauses) { if (ts.isCaseClause(c)) expression(c.expression, locals); c.statements.forEach(x => statement(x, locals)) }
      return
    }
    if ((ts.isBreakStatement(st) && !st.label) || ts.isEmptyStatement(st)) return
    refuse(st, 'standalone: effects or unsupported statement')
  }
  const functionBody = (fn: ts.FunctionLikeDeclaration): void => {
    if (active.has(fn)) refuse(fn, 'standalone: recursion is outside the subset')
    if (done.has(fn)) return
    if (!fn.body || fn.asteriskToken || fn.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) refuse(fn, 'standalone: async, generator or missing body')
    if ((ts.isFunctionDeclaration(fn) || ts.isFunctionExpression(fn)) && fn.name && reserved(fn.name.text)) refuse(fn.name, 'standalone: reserved function name')
    const locals = new Set<ts.Symbol>()
    for (const p of fn.parameters) {
      if (!ts.isIdentifier(p.name) || p.dotDotDotToken || p.initializer) refuse(p, 'standalone: rest, destructuring and defaults are outside the subset')
      if (reserved(p.name.getText())) refuse(p, `standalone: reserved parameter ${p.name.getText()}`)
      const sym = symbol(p.name as ts.Identifier)
      if (locals.has(sym)) refuse(p, 'standalone: duplicate parameter binding')
      locals.add(sym)
    }
    active.add(fn)
    if (ts.isBlock(fn.body!)) statement(fn.body!, locals); else expression(fn.body! as ts.Expression, locals)
    active.delete(fn); done.add(fn)
    const b = [...bindings.values()].find(x => functionOf(x) === fn)
    if (b) reached.add(b.decl.name!.getText())
  }
  functionBody(entry)
  return [...reached].sort()
}
