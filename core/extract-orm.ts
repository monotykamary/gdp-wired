import ts from 'typescript'
import {Refusal} from './extract-read.ts'
import {asset, extractStep, node, type SModule, type SS, type SX, type SType, type StepOptions} from './extract-step.ts'

/** Explicit boundary: the first argument is the injected Prisma client or TypeORM repository. */
export type OrmOptions = {schema: string, model: string, kind?: 'prisma' | 'typeorm'}

export function extractOrm(file: string, code: string, opts: StepOptions & {orm: OrmOptions}) {
  const {readFileSync} = node<{readFileSync: (path: string, encoding: string) => string}>('node:fs')
  const {resolve, dirname, basename} = node<{resolve: (...paths: string[]) => string, dirname: (path: string) => string, basename: (path: string) => string}>('node:path')
  const sf = ts.createSourceFile(file, code, ts.ScriptTarget.Latest, true)
  const fail = (n: ts.Node, why: string): never => { const p = sf.getLineAndCharacterOfPosition(n.getStart(sf)); throw new Refusal(`${file}:${p.line + 1}:${p.character + 1}`, why) }
  try {
    const names = typeof opts.entry === 'string' ? [opts.entry] : opts.entry
    if (!names?.length || new Set(names).size !== names.length) throw new Refusal(file, 'ORM extraction requires distinct explicit entries')
    const model = opts.orm.model, kind = opts.orm.kind ?? 'prisma'
    if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(model)) throw new Refusal(file, 'invalid ORM model name')
    let schema: string
    try { schema = readFileSync(resolve(dirname(file), opts.orm.schema), 'utf8') } catch { throw new Refusal(file, 'ORM schema file cannot be read') }
    const fields: {name: string, t: SType}[] = [], keys: string[] = []
    if (kind === 'prisma') {
      // Mask comments and strings before locating a model; neither can declare one.
      const masked = schema.replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*|"(?:\\.|[^"\\])*"/g, s => s.replace(/[^\n]/g, ' '))
      const blocks = [...masked.matchAll(new RegExp(`\\bmodel\\s+${model}\\s*\\{([^{}]*)\\}`, 'g'))]
      if (blocks.length !== 1) throw new Refusal(file, `expected exactly one Prisma model ${model} in schema`)
      const originalBlock = schema.slice(blocks[0]!.index!, blocks[0]!.index! + blocks[0]![0].length).replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*/g, '')
      if (originalBlock.includes('"') || originalBlock.includes("'")) throw new Refusal(file, `${model}: string syntax in model is unsupported`)
      for (const raw of blocks[0]![1]!.split('\n')) {
        const line = raw.replace(/\/\/.*$/, '').trim(); if (!line) continue
        const m = /^(\w+)\s+(Int|Boolean|String)\s*(.*)$/.exec(line)
        if (!m || /@(?!id\b)/.test(m[3]!) || /[^\s]/.test(m[3]!.replace('@id', ''))) throw new Refusal(file, `${model}: unsupported schema field ${line}`)
        fields.push({name: m[1]!, t: {k: m[2] === 'Int' ? 'int' : m[2] === 'Boolean' ? 'bool' : 'str'}})
        if (m[3]!.includes('@id')) keys.push(m[1]!)
      }
    } else {
      const entity = ts.createSourceFile(opts.orm.schema, schema, ts.ScriptTarget.Latest, true)
      const imports = entity.statements.filter(ts.isImportDeclaration).filter(s => ts.isStringLiteral(s.moduleSpecifier) && s.moduleSpecifier.text === 'typeorm')
      const imported = new Set(imports.flatMap(s => { const b = s.importClause?.namedBindings; return b && ts.isNamedImports(b) && !s.importClause?.isTypeOnly ? b.elements.filter(e => !e.isTypeOnly && !e.propertyName).map(e => e.name.text) : [] }))
      if (!['Entity', 'Column', 'PrimaryColumn'].every(n => imported.has(n))) throw new Refusal(file, `${model}: decorators must be direct named imports from typeorm`)
      if (entity.statements.some(s => !ts.isImportDeclaration(s) && !(ts.isClassDeclaration(s) && s.name?.text === model))) throw new Refusal(file, `${model}: unsupported entity module declaration`)
      for (const s of entity.statements.filter(ts.isImportDeclaration)) {
        const b = s.importClause?.namedBindings
        if (b && ts.isNamedImports(b) && b.elements.some(e => ['Entity', 'Column', 'PrimaryColumn'].includes(e.name.text) && (!ts.isStringLiteral(s.moduleSpecifier) || s.moduleSpecifier.text !== 'typeorm' || e.propertyName || e.isTypeOnly || s.importClause?.isTypeOnly))) throw new Refusal(file, `${model}: ambiguous decorator binding`)
      }
      const classes = entity.statements.filter((s): s is ts.ClassDeclaration => ts.isClassDeclaration(s) && s.name?.text === model)
      const cls = classes.length === 1 ? classes[0] : undefined
      const decorators = (n: ts.Node) => ts.canHaveDecorators(n) ? ts.getDecorators(n) ?? [] : []
      const plain = (d: ts.Decorator, name: string) => ts.isCallExpression(d.expression) && ts.isIdentifier(d.expression.expression) && d.expression.expression.text === name && d.expression.arguments.length === 0
      if ((entity as ts.SourceFile & {parseDiagnostics: readonly unknown[]}).parseDiagnostics.length || !cls || cls.heritageClauses?.length || decorators(cls).length !== 1 || !plain(decorators(cls)[0]!, 'Entity')) throw new Refusal(file, `${model}: expected a plain @Entity() class`)
      for (const member of cls.members) {
        if (!ts.isPropertyDeclaration(member) || !ts.isIdentifier(member.name) || member.initializer || member.questionToken || !member.type || member.modifiers?.some(m => m.kind !== ts.SyntaxKind.Decorator && m.kind !== ts.SyntaxKind.DeclareKeyword)) throw new Refusal(file, `${model}: unsupported entity member`)
        const ds = decorators(member), primary = ds.length === 1 && plain(ds[0]!, 'PrimaryColumn')
        if (!primary && !(ds.length === 1 && plain(ds[0]!, 'Column'))) throw new Refusal(file, `${model}.${member.name.text}: unsupported column decorator`)
        const k = member.type.kind === ts.SyntaxKind.NumberKeyword ? 'int' : member.type.kind === ts.SyntaxKind.StringKeyword ? 'str' : member.type.kind === ts.SyntaxKind.BooleanKeyword ? 'bool' : undefined
        if (!k) throw new Refusal(file, `${model}.${member.name.text}: unsupported column type`)
        fields.push({name: member.name.text, t: {k}})
        if (primary) keys.push(member.name.text)
      }
    }
    if (new Set(fields.map(f => f.name)).size !== fields.length || fields.some(f => ['__proto__', 'prototype', 'constructor'].includes(f.name))) throw new Refusal(file, `${model}: duplicate or reserved column name`)
    if (keys.length !== 1 || !fields.some(f => f.name !== keys[0])) throw new Refusal(file, `${model}: requires one explicit primary key and a value column`)
    const key = keys[0]!, rec = `orm.${model}`, funcs: SModule['funcs'] = {}
    const loc = (n: ts.Node) => { const p = sf.getLineAndCharacterOfPosition(n.getStart(sf)); return `${basename(file)}:${p.line + 1}:${p.character + 1}` }
    const v = (n: string, p: string): SX => ({e: 'var', n, p})
    const get = (x: SX, f: string, p: string): SX => ({e: 'get', x, f, p})
    const call = (x: SX, f: string, kw: [string, SX][], p: string): SX => ({e: 'call', f: get(x, f, p), args: [], kw, p, text: f})
    const manager = (p: string) => get({e: 'cls', rec, p}, 'objects', p)
    const object = (n: ts.Expression): Map<string, ts.Expression> => {
      if (!ts.isObjectLiteralExpression(n)) return fail(n, 'ORM arguments must be explicit object literals')
      const out = new Map<string, ts.Expression>()
      for (const prop of n.properties) {
        if (ts.isShorthandPropertyAssignment(prop)) { if (out.has(prop.name.text)) fail(prop, 'duplicate property'); out.set(prop.name.text, prop.name); continue }
        if (!ts.isPropertyAssignment(prop) || !ts.isIdentifier(prop.name)) return fail(prop, 'ORM properties must be explicit names')
        if (out.has(prop.name.text)) fail(prop, 'duplicate property'); out.set(prop.name.text, prop.initializer)
      }
      return out
    }
    let scalarNames = new Set<string>(), rowName: string | undefined
    const expr = (n: ts.Expression): SX => {
      const p = loc(n)
      if (ts.isIdentifier(n)) { if (!scalarNames.has(n.text)) fail(n, 'only scalar inputs may be used as values'); return v(n.text, p) }
      if (ts.isNumericLiteral(n) && Number.isSafeInteger(Number(n.text))) return {e: 'int', v: n.text, p}
      if (ts.isStringLiteral(n)) return {e: 'str', v: n.text, p}
      if (n.kind === ts.SyntaxKind.TrueKeyword || n.kind === ts.SyntaxKind.FalseKeyword) return {e: 'bool', v: n.kind === ts.SyntaxKind.TrueKeyword, p}
      if (ts.isPropertyAccessExpression(n) && !n.questionDotToken && ts.isIdentifier(n.expression) && n.expression.text === rowName && fields.some(f => f.name === n.name.text)) return get(v(rowName!, p), n.name.text, p)
      if (ts.isParenthesizedExpression(n)) return expr(n.expression)
      return fail(n, 'expression outside the ORM subset')
    }
    for (const name of names) {
      const parts = name.split('.')
      let fn: ts.FunctionDeclaration | ts.MethodDeclaration | undefined
      if (parts.length === 1) {
        const found = sf.statements.filter((s): s is ts.FunctionDeclaration => ts.isFunctionDeclaration(s) && s.name?.text === name)
        if (found.length === 1 && found[0]!.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) fn = found[0]
      } else if (parts.length === 2) {
        const classes = sf.statements.filter((s): s is ts.ClassDeclaration => ts.isClassDeclaration(s) && s.name?.text === parts[0])
        const cls = classes.length === 1 ? classes[0] : undefined
        if (!cls || !cls.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword) || cls.heritageClauses?.length || cls.members.some(m => !ts.isMethodDeclaration(m)) || (ts.canHaveDecorators(cls) && ts.getDecorators(cls)?.length)) throw new Refusal(file, `${name}: expected an exported plain class without constructor or fields`)
        const methods = cls.members.filter((m): m is ts.MethodDeclaration => ts.isMethodDeclaration(m) && ts.isIdentifier(m.name) && m.name.text === parts[1])
        if (methods.length === 1 && !methods[0]!.modifiers?.some(m => m.kind !== ts.SyntaxKind.AsyncKeyword && m.kind !== ts.SyntaxKind.PublicKeyword)) fn = methods[0]
      }
      if (!fn?.body || fn.asteriskToken || fn.modifiers?.some(m => m.kind === ts.SyntaxKind.DefaultKeyword || m.kind === ts.SyntaxKind.DeclareKeyword)) throw new Refusal(file, `${name}: expected an exported non-generator function or plain service method`)
      const dep = fn.parameters[0]; if (!dep || !ts.isIdentifier(dep.name) || dep.dotDotDotToken || dep.initializer) fail(fn, 'first argument must be the injected ORM client')
      const client = (dep!.name as ts.Identifier).text
      if (dep!.questionToken || client === 'this' || client.startsWith('__orm_')) fail(dep!, 'invalid ORM client binding')
      const bindings = new Set([client])
      rowName = undefined
      const params = fn.parameters.slice(1).map(pa => {
        if (!ts.isIdentifier(pa.name) || pa.initializer || pa.questionToken || pa.dotDotDotToken || !pa.type || (pa.name.text === 'this' || pa.name.text.startsWith('__orm_')) || bindings.has(pa.name.text)) return fail(pa, 'ORM inputs require distinct scalar type annotations')
        bindings.add(pa.name.text)
        const k = pa.type.kind === ts.SyntaxKind.NumberKeyword ? 'int' : pa.type.kind === ts.SyntaxKind.StringKeyword ? 'str' : pa.type.kind === ts.SyntaxKind.BooleanKeyword ? 'bool' : undefined
        if (!k) return fail(pa, 'ORM inputs require number, string or boolean')
        return {name: pa.name.text, t: {k} as SType}
      })
      scalarNames = new Set([...bindings].filter(n => n !== client))
      const body: SS[] = []
      for (const [index, st] of fn.body.statements.entries()) {
        if (ts.isReturnStatement(st)) { body.push({s: 'ret', p: loc(st), ...(st.expression ? {x: expr(st.expression)} : {})}); continue }
        let a: ts.Expression | undefined, target: string | undefined
        if (ts.isVariableStatement(st) && st.declarationList.declarations.length === 1) { const d = st.declarationList.declarations[0]!; if (!ts.isIdentifier(d.name)) fail(d, 'expected a row variable'); target = (d.name as ts.Identifier).text; if (bindings.has(target) || target.startsWith('__orm_')) fail(d, 'ORM row binding shadows another binding'); bindings.add(target); a = d.initializer }
        else if (ts.isExpressionStatement(st)) a = st.expression
        if (!a || !ts.isAwaitExpression(a) || !ts.isCallExpression(a.expression)) fail(st, 'only awaited ORM operations and scalar returns are supported')
        const c = (a as ts.AwaitExpression).expression as ts.CallExpression, p = loc(st)
        if (!ts.isPropertyAccessExpression(c.expression) || c.questionDotToken || c.expression.questionDotToken || c.arguments.length !== 1) fail(c, 'unsupported ORM call')
        const access = c.expression as ts.PropertyAccessExpression, op = access.name.text
        const receiver = access.expression.getText(sf)
        if (receiver !== (kind === 'prisma' ? `${client}.${model[0]!.toLowerCase()}${model.slice(1)}` : client)) fail(c, 'ORM receiver must be the injected client and selected model')
        const args = object(c.arguments[0]!)
        const pair = (map: Map<string, ts.Expression>): [string, SX][] => [...map].map(([k, x]) => [k, expr(x)])
        if (kind === 'prisma' && op === 'create') {
          if (target || args.size !== 1 || !args.has('data')) fail(c, 'create result must be unused and only data supplied')
          body.push({s: 'expr', p, x: call(manager(p), 'create', pair(object(args.get('data')!)), p)})
        } else if ((kind === 'prisma' && op === 'findUnique') || (kind === 'typeorm' && op === 'findOneBy')) {
          const where = kind === 'prisma' ? (args.size === 1 && args.has('where') ? object(args.get('where')!) : fail(c, 'findUnique requires only where')) : args
          if (!target || where.size !== 1 || !where.has(key)) fail(c, `read requires an assigned row and exactly its primary key ${JSON.stringify(key)}; received where fields: ${[...where.keys()].map(k => JSON.stringify(k)).join(', ') || '(none)'}`)
          // findUnique/findOneBy return null, whereas the step IR's get fails on absence.
          // This equivalence holds only when the very next operation dereferences the row.
          const next = fn.body.statements[index + 1]
          if (!next || !ts.isReturnStatement(next) || !next.expression || !ts.isPropertyAccessExpression(next.expression) || !ts.isIdentifier(next.expression.expression) || next.expression.expression.text !== target || index + 2 !== fn.body.statements.length) fail(c, 'nullable ORM read must be immediately returned as a row field')
          rowName = target
          body.push({s: 'set', p, to: v(target!, p), x: call(manager(p), 'get', pair(where), p)})
        } else if (kind === 'prisma' && op === 'update') {
          if (target || args.size !== 2 || !args.has('where') || !args.has('data')) fail(c, 'update requires where and data; its result must be unused')
          const where = object(args.get('where')!), data = object(args.get('data')!), row = `__orm_row_${body.length}`
          if (where.size !== 1 || !where.has(key) || data.has(key) || !data.size || [...data.keys()].some(k => !fields.some(f => f.name === k))) fail(c, `update requires primary key ${JSON.stringify(key)} and known non-key columns; received where fields: ${[...where.keys()].map(k => JSON.stringify(k)).join(', ') || '(none)'}; received data fields: ${[...data.keys()].map(k => JSON.stringify(k)).join(', ') || '(none)'}`)
          body.push({s: 'set', p, to: v(row, p), x: call(manager(p), 'get', pair(where), p)})
          for (const [f, x] of data) body.push({s: 'set', p, to: get(v(row, p), f, p), x: expr(x)})
          body.push({s: 'expr', p, x: call(v(row, p), 'save', [], p)})
        } else if (kind === 'typeorm' && op === 'save') {
          if (target) fail(c, 'save result must be unused')
          const row = `__orm_row_${body.length}`
          body.push({s: 'set', p, to: v(row, p), x: {e: 'call', f: {e: 'cls', rec, p}, args: [], kw: pair(args), p}})
          body.push({s: 'expr', p, x: call(v(row, p), 'save', [], p)})
        } else fail(c, `unsupported ORM operation ${op}`)
      }
      funcs[name] = {id: name, name, p: loc(fn), span: [basename(file), sf.getLineAndCharacterOfPosition(fn.getStart()).line + 1, sf.getLineAndCharacterOfPosition(fn.end).line + 1], params, ret: {k: 'any'}, body, decorators: []}
    }
    const mod: SModule = {lang: 'TypeScript', file, path: resolve(file), root: resolve(dirname(file)), module: basename(file), entries: names.map(id => ({k: 'func', id})), funcs, recs: {[rec]: {name: rec, short: model, fields, methods: {}, kinds: [], own: true, module: basename(file), p: file, orm: {framework: kind, key}}}}
    const x = extractStep(mod, () => ({cmd: 'bun', args: [asset('orm/harness.js')], hello: {path: resolve(file), model, kind}}), {...opts, strict: true})
    x.notes.push(`${kind}: injected client, explicit primary keys; database constraints, defaults and triggers are outside the boundary. Importing the original module executes its initialization and imported code with the checker's privileges; the check is not a sandbox and cannot prove absence of external side effects.`)
    return x
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
}
