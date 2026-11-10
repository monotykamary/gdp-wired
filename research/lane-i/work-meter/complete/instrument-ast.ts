import {strict as assert} from 'node:assert'
import {readdirSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
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
  try {
    const printed = ts.createPrinter({removeComments: true}).printFile(changed.transformed[0]!)
    const parsed = ts.createSourceFile(path, printed, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS), parts: string[] = []
    const visit = (node: ts.Node) => {
      const children = node.getChildren(parsed), kind = ts.SyntaxKind[node.kind]
      parts.push(kind + (children.length || node.kind === ts.SyntaxKind.SyntaxList ? '' : ':' + JSON.stringify(node.getText(parsed))))
      for (const child of children) visit(child)
      if (children.length) parts.push('/' + kind)
    }
    visit(parsed)
    return parts.join('\n')
  } finally { changed.dispose() }
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
  const lastImport = file.statements.filter(ts.isImportDeclaration).at(-1)
  const at = lastImport?.end ?? 0
  let module = relative(dirname(path), path.startsWith('kernel/') ? 'kernel/meter.ts' : 'core/meter.ts').replaceAll('\\', '/')
  if (!module.startsWith('.')) module = './' + module
  // Imports can occur after executable declarations. Apply every insertion in
  // the same original coordinate space, including the new import.
  positions.push({at, text: `\nimport {observeAst} from '${module}'\n`})
  let next = file.text
  for (const p of positions.sort((a, b) => b.at - a.at)) next = next.slice(0, p.at) + p.text + next.slice(p.at)
  const erased = canonical(next, path, true), original = canonical(file.text, path, false)
  if (erased !== original) {
    const a = erased.split('\n'), b = original.split('\n'), first = a.findIndex((line, i) => line !== b[i])
    console.error('AST_ERASURE_MISMATCH ' + JSON.stringify({path, line: first + 1, actual: a.slice(Math.max(0, first - 2), first + 3), expected: b.slice(Math.max(0, first - 2), first + 3)}))
    throw new Error('constructor erasure mismatch: ' + path)
  }
  writeFileSync(path, next)
  const blob = (text: string) => execFileSync('git', ['hash-object', '--stdin'], {input: text, encoding: 'utf8'}).trim()
  rows.push({path, sites, before: blob(file.text), after: blob(next)})
}
assert(rows.some(r => r.path === 'kernel/kernel.ts'))
assert(rows.some(r => r.path === 'core/machine.ts'))
console.log('AST_CONSTRUCTOR_AUDIT ' + JSON.stringify({passed: true, semantics: 'identity wrapper after child evaluation; only newly allocated nodes charged', sites: rows.reduce((n, r) => n + r.sites, 0), files: rows}))
// This is a generated source artifact, not a benchmark receipt. No local compilation is needed to apply it.
execFileSync('git', ['add', '--', 'core', 'kernel', 'scripts/test-shards.ts'])
const patch = execFileSync('git', ['diff', '--cached', '--binary', 'HEAD', '--', 'core', 'kernel', 'scripts/test-shards.ts'], {encoding: 'utf8', maxBuffer: 16 * 1024 * 1024})
const packed = gzipSync(patch).toString('base64'), chunks = packed.match(/.{1,12000}/g) ?? []
console.log('AST_SOURCE_META ' + JSON.stringify({rawBytes: Buffer.byteLength(patch), sha256: createHash('sha256').update(patch).digest('hex'), encoding: 'gzip-base64', chunks: chunks.length}))
for (const [index, data] of chunks.entries()) console.log(`AST_SOURCE_CHUNK ${index} ${data}`)
console.log('AST_SOURCE_END ' + chunks.length)
