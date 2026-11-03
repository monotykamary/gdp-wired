import ts from 'typescript'

export type Operator = 'remove-guard' | 'invert-guard' | 'wrong-key' | 'relax-boundary' | 'weaken-isolation' | 'remove-lock' | 'narrow-transaction' | 'split-compare-set'
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
  const strip = (e: ts.Expression): ts.Expression => ts.isParenthesizedExpression(e) || ts.isAsExpression(e) ? strip(e.expression) : e
  const genBody = (e: ts.Expression | undefined): ts.Block | undefined => {
    if (!e || !ts.isCallExpression(e) || e.expression.getText(sf) !== 'Effect.gen') return undefined
    const fn = e.arguments[0]
    return fn && ts.isFunctionExpression(fn) && ts.isBlock(fn.body) ? fn.body : undefined
  }
  const visit = (n: ts.Node, method?: ts.MethodDeclaration) => {
    // Unwrap a lock around a generator's body, retaining the actual operation statements.
    // Hoisting (rather than another nested generator) keeps each source operation observable.
    if (ts.isExpressionStatement(n) && ts.isYieldExpression(n.expression) && n.expression.expression) {
      const call = strip(n.expression.expression)
      if (ts.isCallExpression(call)) {
        const callee = strip(call.expression)
        const body = genBody(call.arguments[0])
        if (body && ts.isCallExpression(callee) && ts.isPropertyAccessExpression(callee.expression) && callee.expression.name.text === 'withPermits'
          && callee.arguments.length === 1 && callee.arguments[0]!.getText(sf) === '1') {
          add('remove-lock', n.getStart(sf), n.end, body.statements.map(s => s.getText(sf)).join('\n'))
        }
        // Move a transaction's leading read outside, leaving every subsequent statement inside.
        if (body && callee.getText(sf) === 'Effect.tx' && body.statements.length > 1) {
          const first = body.statements[0]!
          if (ts.isVariableStatement(first) && first.declarationList.declarations.length === 1) {
            const init = first.declarationList.declarations[0]!.initializer
            if (init && ts.isYieldExpression(init) && init.expression && ts.isCallExpression(init.expression) && /^(TxRef|TRef|Ref)\.get$/.test(init.expression.expression.getText(sf))) {
              const narrowed = source.slice(n.getStart(sf), first.getStart(sf)) + source.slice(first.end, n.end)
              add('narrow-transaction', n.getStart(sf), n.end, first.getText(sf) + '\n' + narrowed)
            }
          }
        }
      }
    }
    // Split a scalar compare-and-set expressed as modify(ref, old => [success, next]).
    if (ts.isVariableStatement(n) && n.declarationList.declarations.length === 1) {
      const d = n.declarationList.declarations[0]!, init = d.initializer
      if (ts.isIdentifier(d.name) && init && ts.isYieldExpression(init) && init.expression && ts.isCallExpression(init.expression)) {
        const call = init.expression, api = call.expression.getText(sf), fn = call.arguments[1]
        if (/^(TxRef|TRef|Ref)\.modify$/.test(api) && call.arguments.length === 2 && fn && ts.isArrowFunction(fn) && fn.parameters.length === 1 && ts.isIdentifier(fn.parameters[0]!.name) && !ts.isBlock(fn.body)) {
          const tuple = strip(fn.body), param = fn.parameters[0]!.name.text
          if (ts.isArrayLiteralExpression(tuple) && tuple.elements.length === 2) {
            let fresh = `mutationRead${n.getStart(sf)}`
            while (source.includes(fresh)) fresh += '_'
            const substitute = (e: ts.Expression) => {
              const edits: [number, number][] = []
              const scan = (x: ts.Node) => {
                if (ts.isIdentifier(x) && x.text === param && !(ts.isPropertyAccessExpression(x.parent) && x.parent.name === x)) edits.push([x.getStart(sf) - e.getStart(sf), x.end - e.getStart(sf)])
                ts.forEachChild(x, scan)
              }
              scan(e)
              let text = e.getText(sf)
              for (const [a, b] of edits.sort((x, y) => y[0] - x[0])) text = text.slice(0, a) + fresh + text.slice(b)
              return text
            }
            const ref = call.arguments[0]!.getText(sf), prefix = api.split('.')[0]!
            add('split-compare-set', n.getStart(sf), n.end,
              `const ${fresh} = yield* ${prefix}.get(${ref})\nyield* ${prefix}.set(${ref}, ${substitute(tuple.elements[1]!)})\nconst ${d.name.text} = ${substitute(tuple.elements[0]!)}`)
          }
        }
      }
    }

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
