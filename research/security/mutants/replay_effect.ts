import ts from 'typescript'
import * as runtime from 'effect'
import {readFileSync, writeFileSync, unlinkSync} from 'node:fs'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {createHash, randomUUID} from 'node:crypto'
import {holds, parseCall, type Call, type Replay} from './replay.ts'

// The source's original Ref/TxRef operations, locks and transactions execute on Effect itself.
// Insert scheduling gates only BETWEEN outer source operations; never inside a critical section.
// The only other instrumentation exposes the factory's existing refs for observation.
type Instrumented = {code: string, units: Record<string, number>, refs: string[], parameters: Record<string, string[]>}
export function instrumentEffect(source: string, entry: string, token: string): Instrumented {
  if (source.includes('__mutation')) throw new Error('reserved replay instrumentation name in source')
  const sf = ts.createSourceFile('module.ts', source, ts.ScriptTarget.Latest, true)
  const declarations: ts.VariableDeclaration[] = []
  const walk = (n: ts.Node) => { if (ts.isVariableDeclaration(n)) declarations.push(n); ts.forEachChild(n, walk) }
  walk(sf)
  const factory = declarations.find(d => ts.isIdentifier(d.name) && d.name.text === entry)
  const make = factory?.initializer
  if (!make || !ts.isCallExpression(make) || make.expression.getText(sf) !== 'Effect.gen') throw new Error('replay requires a canonical Effect.gen factory')
  const body = make.arguments[0]
  if (!body || !ts.isFunctionExpression(body)) throw new Error('factory generator missing')
  const ret = body.body.statements.at(-1)
  if (!ret || !ts.isReturnStatement(ret) || !ret.expression || !ts.isObjectLiteralExpression(ret.expression)) throw new Error('factory must return its service object')
  const object = ret.expression
  const exported = new Set(object.properties.map(p => {
    if (!ts.isShorthandPropertyAssignment(p)) throw new Error('replay requires shorthand service methods')
    return p.name.text
  }))
  const edits: {at: number, text: string}[] = [], units: Record<string, number> = {}, parameters: Record<string, string[]> = {}, refs: string[] = [], exposed: string[] = []
  for (const statement of body.body.statements) {
    if (!ts.isVariableStatement(statement)) continue
    for (const d of statement.declarationList.declarations) {
      if (!ts.isIdentifier(d.name) || !d.initializer) continue
      const init = d.initializer, name = d.name.text
      if (ts.isYieldExpression(init) && init.expression && ts.isCallExpression(init.expression)) {
        const api = /^(TxRef|Ref)\.make$/.exec(init.expression.expression.getText(sf))?.[1]
        if (api) { refs.push(name); exposed.push(`${JSON.stringify(name)}: {api: ${JSON.stringify(api)}, ref: ${name}}`) }
      }
      if (!exported.has(name)) continue
      if (!ts.isCallExpression(init) || !ts.isCallExpression(init.expression) || init.expression.expression.getText(sf) !== 'Effect.fn') throw new Error('replay requires Effect.fn service methods')
      const fn = init.arguments[0]
      if (!fn || !ts.isFunctionExpression(fn)) throw new Error('service generator missing')
      const statements = [...fn.body.statements], points: number[] = []
      // Count outer yields. Functions passed to a lock/transaction remain opaque and atomic.
      const yields = (n: ts.Node): number => {
        if (ts.isFunctionLike(n)) return 0
        if (ts.isYieldExpression(n)) return 1
        let count = 0
        ts.forEachChild(n, c => { count += yields(c) })
        return count
      }
      statements.forEach((s, i) => {
        const count = yields(s)
        if (count > 1) throw new Error('multiple outer operations in one statement are outside replay subset')
        if (count) points.push(i)
      })
      if (!points.length) throw new Error('service method has no observable operation')
      units[name] = points.length
      parameters[name] = fn.parameters.map(p => {
        if (!ts.isIdentifier(p.name)) throw new Error('destructured arguments are outside replay subset')
        return p.name.text
      })
      edits.push({at: fn.parameters.end, text: `${fn.parameters.length ? ', ' : ''}__mutationFiber: number`})
      points.forEach((point, index) => {
        const start = index === 0 ? 0 : points[index - 1]! + 1
        const end = index === points.length - 1 ? statements.length - 1 : point
        edits.push({at: statements[start]!.getStart(sf), text: `yield* __mutationBefore(__mutationFiber, ${index + 1});\n`})
        edits.push({at: statements[end]!.end, text: `\nyield* __mutationAfter(__mutationFiber, ${index + 1});\n`})
      })
    }
  }
  if (Object.keys(units).length !== exported.size || !refs.length) throw new Error('not every service method/ref was instrumented')
  edits.push({at: object.end - 1, text: `${object.properties.hasTrailingComma ? '' : ','} __mutationRefs: {${exposed.join(', ')}}`})
  let code = source
  for (const edit of edits.sort((a, b) => b.at - a.at)) code = code.slice(0, edit.at) + edit.text + code.slice(edit.at)
  code = `import {Effect as __mutationEffect} from 'effect';\nconst __mutationControl = (globalThis as any)[Symbol.for(${JSON.stringify(token)})];\nconst __mutationBefore = (fiber: number, step: number) => __mutationEffect.promise(() => __mutationControl.before(fiber, step));\nconst __mutationAfter = (fiber: number, step: number) => __mutationEffect.sync(() => __mutationControl.after(fiber, step));\n` + code
  return {code, units, refs, parameters}
}

type Deferred = {promise: Promise<void>, resolve: () => void}
const deferred = (): Deferred => { let resolve!: () => void; const promise = new Promise<void>(r => { resolve = r }); return {promise, resolve} }
const bounded = async (p: Promise<unknown>) => {
  let timer: ReturnType<typeof setTimeout> | undefined
  try { return await Promise.race([p, new Promise((_, reject) => { timer = setTimeout(() => reject(new Error('source fiber did not reach its scheduled boundary')), 5000) })]) }
  finally { clearTimeout(timer) }
}
type Action = {id: number, method: string, step: number, total: number, call?: Call}
function actionsOf(lines: string[]): Action[] {
  return lines.map(line => {
    const m = /^fiber (\d+): (.*?)(?:, its step (\d+) of (\d+))?$/.exec(line)
    if (!m) throw new Error('missing fiber identity in source witness')
    const start = m[2]!.includes('('), call = start ? parseCall(m[2]!) : undefined
    return {id: Number(m[1]), method: call?.method ?? m[2]!, step: Number(m[3] ?? 1), total: Number(m[4] ?? 1), call}
  })
}
type Fiber = {call: Call, ready: Deferred, progress: Deferred, waiting?: {step: number, release: () => void}, done: boolean, error?: unknown, abort: AbortController, promise?: Promise<void>}
type EffectReplay = Replay & {schedule?: string, sourceSha256?: string, boundaries?: Record<string, number>}

export async function replayEffect(file: string, entry: string, expr: string, lines: string[], directory: string, parent = false): Promise<EffectReplay> {
  const source = readFileSync(file, 'utf8'), token = `security-replay-${randomUUID()}`, path = join(directory, token + '.ts')
  const fibers = new Map<number, Fiber>(), steps: unknown[] = []
  const global = globalThis as unknown as Record<symbol, unknown>
  try {
    const plan = actionsOf(lines)
    if (!plan.length || plan.length > 128) throw new Error('missing or oversized fiber witness')
    const instrumented = instrumentEffect(source, entry, token)
    global[Symbol.for(token)] = {
      before: (id: number, step: number) => {
        const fiber = fibers.get(id)
        if (!fiber || fiber.done || fiber.waiting) throw new Error('unexpected source fiber boundary')
        return new Promise<void>(release => { fiber.waiting = {step, release}; fiber.ready.resolve() })
      },
      after: (id: number, step: number) => {
        const fiber = fibers.get(id)
        if (!fiber || fiber.waiting || step < 1) throw new Error('unexpected source operation completion')
        fiber.progress.resolve()
      },
    }
    writeFileSync(path, instrumented.code)
    // Loading executes the original module with observation/scheduling hooks, not the extracted rule.
    const module = await import(pathToFileURL(path).href) as Record<string, unknown>
    const service = await runtime.Effect.runPromise(module[entry] as runtime.Effect.Effect<Record<string, unknown>>)
    const observed = service.__mutationRefs as Record<string, {api: 'TxRef' | 'Ref', ref: unknown}>
    const snapshot = async () => {
      const values: Record<string, unknown> = {}
      for (const [name, ref] of Object.entries(observed)) {
        const operation = ref.api === 'TxRef' ? runtime.TxRef.get(ref.ref as runtime.TxRef.TxRef<unknown>) : runtime.Ref.get(ref.ref as runtime.Ref.Ref<unknown>)
        values[name] = await runtime.Effect.runPromise(operation)
      }
      return values
    }
    const launch = async (a: Action) => {
      if (!a.call || a.step !== 1) throw new Error('a source call must start at step one')
      const previous = fibers.get(a.id)
      if (previous && !previous.done) await bounded(previous.promise!)
      const fiber: Fiber = {call: a.call, ready: deferred(), progress: deferred(), done: false, abort: new AbortController()}
      fibers.set(a.id, fiber)
      const fn = service[a.method]
      if (typeof fn !== 'function') throw new Error('witness names no service method')
      const names = instrumented.parameters[a.method]!
      if (names.length !== Object.keys(a.call.args).length || names.some(n => !Object.hasOwn(a.call!.args, n))) throw new Error('witness arguments differ from the source signature')
      const operation = Reflect.apply(fn, service, [...names.map(n => a.call!.args[n]), a.id]) as runtime.Effect.Effect<unknown>
      fiber.promise = runtime.Effect.runPromise(operation, {signal: fiber.abort.signal}).then(() => { fiber.done = true; fiber.progress.resolve(); fiber.ready.resolve() }, (error: unknown) => { fiber.error = error; fiber.done = true; fiber.progress.resolve(); fiber.ready.resolve() })
      return fiber
    }
    let broken = false
    const advance = async (fiber: Fiber, a: Action) => {
      await bounded(fiber.ready.promise)
      if (fiber.done || fiber.error || fiber.waiting?.step !== a.step) throw new Error('source does not match the scheduled operation')
      const before = await snapshot(), release = fiber.waiting.release
      fiber.waiting = undefined
      fiber.ready = deferred()
      fiber.progress = deferred()
      release()
      await bounded(fiber.progress.promise)
      if (fiber.error) throw new Error('source operation failed: ' + (fiber.error instanceof Error ? fiber.error.message : JSON.stringify(fiber.error) ?? 'unknown failure'))
      const after = await snapshot()
      broken ||= !holds(expr, before, after)
      steps.push({fiber: a.id, method: a.method, step: a.step, before, after})
    }
    if (parent) {
      // Changed atomic boundaries cannot take the mutant's illegal interleaving. Reproduce its
      // same calls in start order under the clean source's real boundaries, explicitly labelled.
      for (const a of plan.filter(a => a.call)) {
        const fiber = await launch(a)
        for (let step = 1; step <= instrumented.units[a.method]! && !fiber.done; step++) await advance(fiber, {...a, step})
        await bounded(fiber.promise!)
        if (fiber.error) throw new Error('clean source call failed')
      }
    } else {
      for (const a of plan) {
        if (instrumented.units[a.method] !== a.total) throw new Error('source boundary count differs from the witness')
        const fiber = a.call ? await launch(a) : fibers.get(a.id)
        if (!fiber || fiber.call.method !== a.method) throw new Error('witness resumes a different call')
        await advance(fiber, a)
      }
    }
    return {ok: true, broken, steps, schedule: parent ? 'same calls serialized under clean source boundaries' : 'exact fiber counterexample',
      sourceSha256: createHash('sha256').update(source).digest('hex'), boundaries: instrumented.units}
  } catch (e) { return {ok: false, broken: false, steps, why: e instanceof Error ? e.message : String(e)} }
  finally {
    for (const fiber of fibers.values()) { fiber.abort.abort(); fiber.waiting?.release() }
    await Promise.allSettled([...fibers.values()].flatMap(f => f.promise ? [f.promise] : []))
    delete global[Symbol.for(token)]
    try { unlinkSync(path) } catch { /* module creation may have failed */ }
  }
}
