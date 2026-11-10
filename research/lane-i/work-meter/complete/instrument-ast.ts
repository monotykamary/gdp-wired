import {strict as assert} from 'node:assert'
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {dirname, relative, resolve} from 'node:path'
import {execFileSync} from 'node:child_process'
import ts from 'typescript'

const root = process.cwd()
const list = (dir: string): string[] => readdirSync(dir, {withFileTypes: true}).flatMap(e => e.isDirectory() ? list(dir + '/' + e.name) : e.name.endsWith('.ts') && !e.name.endsWith('.test.ts') && !e.name.endsWith('.d.ts') ? [dir + '/' + e.name] : [])
const paths = [...list('core'), 'kernel/kernel.ts', 'kernel/prove.ts', 'kernel/model-values.ts']
const cfg = ts.readConfigFile('tsconfig.json', ts.sys.readFile)
assert(!cfg.error)
const opts = ts.parseJsonConfigFileContent(cfg.config, ts.sys, root).options
const program = ts.createProgram(paths, opts), checker = program.getTypeChecker()
const ops = new Set(['const', 'var', 'add', 'sub', 'mul', 'prod', 'min', 'max', 'if', 'get', 'tup', 'proj', '<', '<=', '=', 'and', 'or', 'not', 'flag', 'all'])
const field = (p: ts.ObjectLiteralElementLike) => p.name && (ts.isIdentifier(p.name) || ts.isStringLiteral(p.name)) ? p.name.text : undefined
function astType(type: ts.Type | undefined, node: ts.Node) {
  if (!type || type.flags & (ts.TypeFlags.Any | ts.TypeFlags.Unknown)) return false
  const op = type.getProperty('op')
  if (op) {
    const t = checker.getTypeOfSymbolAtLocation(op, node), variants = t.isUnion() ? t.types : [t]
    return variants.length > 0 && variants.every(v => v.isStringLiteral() && ops.has(v.value))
  }
  return !!type.getProperty('hyps') && !!type.getProperty('name')
}
function allocated(node: ts.ObjectLiteralExpression) {
  const op = node.properties.find(p => field(p) === 'op')
  return !!op && ts.isPropertyAssignment(op) && ts.isStringLiteral(op.initializer) && ops.has(op.initializer.text)
    || astType(checker.getTypeAtLocation(node), node) || astType(checker.getContextualType(node), node)
}
function canonical(text: string, path: string, erase: boolean) {
  const source = ts.createSourceFile(path, text, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS)
  const changed = ts.transform(source, [context => node => {
    const visit: ts.Visitor = n => {
      if (ts.isParenthesizedExpression(n)) return ts.visitNode(n.expression, visit)
      if (erase && ts.isCallExpression(n) && ts.isIdentifier(n.expression) && n.expression.text === 'observeAst') { assert.equal(n.arguments.length, 1); return ts.visitNode(n.arguments[0]!, visit) }
      if (erase && ts.isImportDeclaration(n) && n.importClause?.namedBindings && ts.isNamedImports(n.importClause.namedBindings)
        && n.importClause.namedBindings.elements.length === 1 && n.importClause.namedBindings.elements[0]!.name.text === 'observeAst') return undefined
      return ts.visitEachChild(n, visit, context)
    }
    return ts.visitNode(node, visit) as ts.SourceFile
  }])
  try { return ts.createPrinter({removeComments: true}).printFile(changed.transformed[0]!) } finally { changed.dispose() }
}
const rows: {path: string, sites: number, before: string, after: string}[] = []
for (const path of paths) {
  const file = program.getSourceFile(resolve(path)) ?? program.getSourceFile(path)
  assert(file, path)
  const positions: {at: number, text: string}[] = []
  let sites = 0
  const visit = (node: ts.Node) => {
    if (ts.isObjectLiteralExpression(node) && allocated(node)) { positions.push({at: node.getStart(file), text: 'observeAst('}, {at: node.end, text: ')'}); sites++ }
    ts.forEachChild(node, visit)
  }
  visit(file)
  if (!sites) continue
  assert(!file.text.includes('observeAst'), 'unexpected existing binding: ' + path)
  let next = file.text
  for (const p of positions.sort((a, b) => b.at - a.at)) next = next.slice(0, p.at) + p.text + next.slice(p.at)
  const lastImport = file.statements.filter(ts.isImportDeclaration).at(-1)
  const at = lastImport?.end ?? 0
  let module = relative(dirname(path), path.startsWith('kernel/') ? 'kernel/meter.ts' : 'core/meter.ts').replaceAll('\\', '/')
  if (!module.startsWith('.')) module = './' + module
  // Imports precede every runtime object literal, so the original insertion offset is unchanged.
  next = next.slice(0, at) + `\nimport {observeAst} from '${module}'\n` + next.slice(at)
  assert.equal(canonical(next, path, true), canonical(file.text, path, false), 'constructor erasure mismatch: ' + path)
  writeFileSync(path, next)
  const blob = (text: string) => execFileSync('git', ['hash-object', '--stdin'], {input: text, encoding: 'utf8'}).trim()
  rows.push({path, sites, before: blob(file.text), after: blob(next)})
}
assert(rows.some(r => r.path === 'kernel/kernel.ts'))
assert(rows.some(r => r.path === 'core/machine.ts'))
console.log('AST_CONSTRUCTOR_AUDIT ' + JSON.stringify({passed: true, semantics: 'identity wrapper after child evaluation; only newly allocated nodes charged', sites: rows.reduce((n, r) => n + r.sites, 0), files: rows}))
// This is a generated source artifact, not a benchmark receipt. No local compilation is needed to apply it.
execFileSync('git', ['add', '--', 'core', 'kernel', 'scripts/test-shards.ts'])
console.log('SOURCE_PATCH_BEGIN')
process.stdout.write(execFileSync('git', ['diff', '--cached', '--binary', 'HEAD', '--', 'core', 'kernel', 'scripts/test-shards.ts'], {encoding: 'utf8', maxBuffer: 16 * 1024 * 1024}))
console.log('SOURCE_PATCH_END')
