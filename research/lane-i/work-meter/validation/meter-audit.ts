import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import ts from 'typescript'

const base = 'b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3'
const names = new Set(['tableCells', 'checkSteps', 'astNodes'])
const source = (text: string, path: string) => ts.createSourceFile(path, text, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS)
function meterExpression(e: ts.Node): boolean {
  return ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken && ts.isPropertyAccessExpression(e.left)
    && ts.isIdentifier(e.left.expression) && e.left.expression.text === 'kernelMeter' && names.has(e.left.name.text)
}
function additive(node: ts.Node): boolean {
  return ts.isExpressionStatement(node) && meterExpression(node.expression)
}
function instrumentation(node: ts.Node): boolean {
  if (additive(node)) return true
  if (ts.isBlock(node)) return node.statements.length > 0 && node.statements.every(instrumentation)
  return ts.isForOfStatement(node) && instrumentation(node.statement)
}
function onlyWrites(file: ts.SourceFile) {
  let writes = 0
  const visit = (node: ts.Node) => {
    if (ts.isIdentifier(node) && node.text === 'kernelMeter') {
      if (ts.isImportSpecifier(node.parent) && node.parent.name === node) return
      const access = node.parent
      assert(ts.isPropertyAccessExpression(access) && access.expression === node, 'meter alias or non-property use')
      const assignment = access.parent
      assert(ts.isBinaryExpression(assignment) && assignment.left === access && assignment.operatorToken.kind === ts.SyntaxKind.PlusEqualsToken, 'meter read or non-additive write')
      const use = assignment.parent
      assert(ts.isExpressionStatement(use) || ts.isBinaryExpression(use) && use.operatorToken.kind === ts.SyntaxKind.CommaToken && use.left === assignment, 'meter assignment result must be discarded')
      assert(names.has(access.name.text), 'unexpected field')
      writes++
    }
    ts.forEachChild(node, visit)
  }
  visit(file)
  assert(writes > 0, 'no instrumented writes')
  return writes
}
function erased(file: ts.SourceFile) {
  const result = ts.transform(file, [context => root => {
    const visit: ts.Visitor = node => {
      if (instrumentation(node)) return undefined
      if (ts.isCallExpression(node) && ts.isIdentifier(node.expression) && node.expression.text === 'observeAst') { assert.equal(node.arguments.length, 1); return ts.visitNode(node.arguments[0]!, visit) }
      if (ts.isParenthesizedExpression(node)) return ts.visitNode(node.expression, visit)
      if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.CommaToken && meterExpression(node.left)) return ts.visitNode(node.right, visit)
      if (ts.isImportDeclaration(node) && node.importClause?.namedBindings && ts.isNamedImports(node.importClause.namedBindings)
        && node.importClause.namedBindings.elements.every(e => e.name.text === 'kernelMeter' || e.name.text === 'observeAst')) return undefined
      return ts.visitEachChild(node, visit, context)
    }
    return ts.visitNode(root, visit) as ts.SourceFile
  }])
  try { return ts.createPrinter({removeComments: true, newLine: ts.NewLineKind.LineFeed}).printFile(result.transformed[0]!) }
  finally { result.dispose() }
}
for (const path of ['kernel/kernel.ts', 'core/check.ts']) {
  const current = source(readFileSync(path, 'utf8'), path), original = source(execFileSync('git', ['show', `${base}:${path}`], {encoding: 'utf8'}), path)
  const writes = onlyWrites(current)
  assert.equal(erased(current), erased(original), 'checker changed after instrumentation erasure: ' + path)
  assert.throws(() => onlyWrites(source(readFileSync(path, 'utf8') + '\nconsole.log(kernelMeter.checkSteps)\n', path)), 'read mutation must be refused')
  assert.throws(() => onlyWrites(source(readFileSync(path, 'utf8') + '\nif (kernelMeter.checkSteps += 1) throw new Error()\n', path)), 'counter-result branch must be refused')
  assert.notEqual(erased(source(readFileSync(path, 'utf8') + '\nconst changedAcceptance = true\n', path)), erased(original), 'non-instrumentation mutation must differ')
  console.log('KERNEL_METER_AST_AUDIT ' + JSON.stringify({path, writes, incrementsOnly: true, readMutationRefused: true, counterResultMutationRefused: true, semanticMutationDetected: true}))
}

const helper = source(readFileSync('kernel/meter.ts', 'utf8'), 'kernel/meter.ts')
const functions = helper.statements.filter(ts.isFunctionDeclaration)
assert.equal(functions.length, 1)
const observe = functions[0]!
assert.equal(observe.name?.text, 'observeAst')
assert.equal(observe.parameters.length, 1)
assert(ts.isIdentifier(observe.parameters[0]!.name) && observe.parameters[0]!.name.text === 'node')
assert(!observe.parameters[0]!.initializer && !observe.parameters[0]!.dotDotDotToken)
assert.equal(observe.body?.statements.length, 2)
const increment = observe.body!.statements[0]!, returned = observe.body!.statements[1]!
assert(ts.isExpressionStatement(increment) && meterExpression(increment.expression))
assert(ts.isBinaryExpression(increment.expression) && ts.isNumericLiteral(increment.expression.right) && increment.expression.right.text === '1')
assert(ts.isPropertyAccessExpression(increment.expression.left) && increment.expression.left.name.text === 'astNodes')
assert(ts.isReturnStatement(returned) && returned.expression && ts.isIdentifier(returned.expression) && returned.expression.text === 'node')
assert(!observe.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword))
console.log('KERNEL_AST_IDENTITY_AUDIT ' + JSON.stringify({passed: true, chargesAfterArgumentEvaluation: true, returnsSameNode: true}))
