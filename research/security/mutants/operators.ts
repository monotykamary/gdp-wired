import ts from 'typescript'

export type Operator = 'remove-guard' | 'invert-guard' | 'wrong-key' | 'relax-boundary' | 'weaken-isolation'
export type Mutation = {id: string, operator: Operator, start: number, end: number, before: string, after: string, source: string}

// One syntactic site per mutant. No filenames, law names or fixture IDs are consulted.
export function mutate(source: string, language: 'ts' | 'py'): Mutation[] {
  const out: Mutation[] = []
  const add = (operator: Operator, start: number, end: number, after: string) => {
    const before = source.slice(start, end)
    if (before === after) return
    out.push({id: `${operator}-${start}-${out.length}`, operator, start, end, before, after, source: source.slice(0, start) + after + source.slice(end)})
  }
  if (language === 'py') {
    for (const m of source.matchAll(/^# gdp: env (atomic|snapshot)\s*$/gm)) {
      const start = m.index! + m[0].indexOf(m[1]!)
      add('weaken-isolation', start, start + m[1]!.length, 'read committed')
    }
    return out
  }
  const sf = ts.createSourceFile('module.ts', source, ts.ScriptTarget.Latest, true)
  const returns = (n: ts.Statement): boolean => ts.isReturnStatement(n) || ts.isBlock(n) && n.statements.length === 1 && ts.isReturnStatement(n.statements[0]!)
  const visit = (n: ts.Node, method?: ts.MethodDeclaration) => {
    if (ts.isConstructorDeclaration(n)) return // constructor validation is not an operation's guard
    if (ts.isMethodDeclaration(n)) method = n
    if (method && ts.isIfStatement(n) && !n.elseStatement && returns(n.thenStatement)) {
      add('remove-guard', n.getStart(sf), n.end, '')
      add('invert-guard', n.expression.getStart(sf), n.expression.end, `!(${n.expression.getText(sf)})`)
      const boundary = (x: ts.Node) => {
        if (ts.isBinaryExpression(x) && x.operatorToken.kind === ts.SyntaxKind.GreaterThanEqualsToken)
          add('relax-boundary', x.operatorToken.getStart(sf), x.operatorToken.end, '>')
        ts.forEachChild(x, boundary)
      }
      boundary(n.expression)
    }
    if (method && ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && ['get', 'set', 'delete', 'has'].includes(n.expression.name.text)) {
      const key = n.arguments[0]
      if (key && ts.isIdentifier(key)) {
        const old = method.parameters.find(p => ts.isIdentifier(p.name) && p.name.text === key.text)
        if (old?.type) for (const replacement of method.parameters) {
          if (replacement !== old && ts.isIdentifier(replacement.name) && replacement.type?.getText(sf) === old.type.getText(sf))
            add('wrong-key', key.getStart(sf), key.end, replacement.name.text)
        }
      }
    }
    ts.forEachChild(n, c => visit(c, method))
  }
  visit(sf)
  return out
}
