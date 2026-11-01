// Effect's concurrency primitives, modelled once (core/effect.ts reads a service through this): a Queue (bounded,
// dropping, sliding, unbounded) and a Semaphore of any number of permits, made by the service's make effect, are written
// again as what Effect's own hold, in transactions over TxRefs (4.x) or TRefs (3.x), and the service read as any:
//   a queue `q`   q_items (a map from position to item), q_head (the items that left: taken, polled, slid out or shut
//                 down), q_tail (the items that came in) and q_open; it holds the items at q_head .. q_tail - 1, oldest
//                 first. offer appends at the tail (a full bounded queue waits, a dropping one answers false, a sliding
//                 one lets its oldest go), take answers the oldest (an empty queue waits), poll an Option of it, size the
//                 count, shutdown drops what it holds.
//   a semaphore   s_taken, the permits taken (Effect's own field), and s_held, those the calling fiber holds (its takes
//                 less its releases; under many fibers one a fiber, summing to s_taken, so a release past what was taken
//                 is a fiber's own): take(n) waits until n are free, release(n) gives n back (unchecked, as Effect does), withPermits(n)(body) is take, the body's
//                 statements, release (a failure in the body releasing first, as its ensuring does).
// Each operation is one transaction, so one atomic step (as the operation is on Effect's runtime), a wait its guard; a
// method of several is several steps, the fibers interleaving them (core/effect.ts's fibered). The model's own laws
// (bounded, nothing lost, FIFO, the permits) are proven once on the canonical service's rule (primitiveRule) and run
// beside the real primitive on random operations and fibers (primitiveConforms); a service's instances carry the laws
// that hold of every use (the queue's bound, at most the permits taken) as invariants, and the one that depends on the
// use (a semaphore never released past what was taken) as a law to prove of it.
import ts from 'typescript'
import * as dsl from './dsl.ts'
import type {StepLaw} from './dsl.ts'
import {type Law, interpret, searchSeeded} from './machine.ts'
import {allowed} from './watch.ts'
import {type Setup, bare as strip, memberName, refuse, text} from './extract-read.ts'
import type {Extraction} from './extract.ts'
import {type EffectOptions, extractEffect} from './effect.ts'

export type Strategy = 'bounded' | 'dropping' | 'sliding' | 'unbounded'
export type Prim =
  | {name: string, kind: 'queue', strategy: Strategy, capacity?: number | string, fields: string[]}
  | {name: string, kind: 'semaphore', permits: number | string, fields: string[]}
type Inst = Prim & {decl: ts.VariableDeclaration, stmt: ts.VariableStatement, item?: string, zero?: string, shuts?: boolean}
type Api = (e: ts.Expression) => string | undefined

const QUEUES: Record<string, Strategy> = {'Queue.bounded': 'bounded', 'Queue.dropping': 'dropping', 'Queue.sliding': 'sliding', 'Queue.unbounded': 'unbounded', 'Queue.make': 'bounded'}
const SEMS = new Set(['Semaphore.make', 'Effect.makeSemaphore', 'Semaphore.makeUnsafe', 'Effect.unsafeMakeSemaphore'])
// What each version's queue answers on its operations (3.x interrupts every one on a shut-down queue; 4.x only take).
const QOPS4 = ['offer', 'take', 'poll', 'size', 'isFull', 'shutdown'], QOPS3 = ['offer', 'take', 'poll', 'shutdown', 'isShutdown']
const FAILS = /^(Effect|STM)\.(fail|failSync|failCause|failCauseSync|die|dieSync|dieMessage|interrupt)$/
export const WAITS_FOREVER = 'an operation that interrupts its fiber on a shut-down queue (every one on Effect 3, take on Effect 4) is read as a wait that never ends: the fiber takes no step after it, which is what an interrupted one does'

// The service's make effect `make` written again with its primitives modelled; undefined where it makes none (or only
// Semaphores of 1 used as locks, read as before: core/effect.ts's lock).
export function rewritePrims(s: Setup, made: {fn: ts.FunctionLikeDeclaration, params: readonly ts.ParameterDeclaration[]}, api: Api, v4: boolean, opts: {params?: boolean} = {}): {code: string, prims: Prim[], notes: string[]} | undefined {
  const make = made.fn
  const sf = s.sf, body = make.body && ts.isBlock(make.body) ? make.body : undefined
  if (!body || !/\b(Queue|Semaphore|makeSemaphore|unsafeMakeSemaphore)\b/.test(sf.text)) return undefined
  const insts: Inst[] = [], params = new Set(made.params.flatMap(p => (ts.isIdentifier(p.name) ? [p.name.text] : [])))
  const whole = (e: ts.Expression | undefined, what: string, at: ts.Node, min: number): number | string => {
    const x = e && strip(e)
    if (x && ts.isNumericLiteral(x) && Number.isInteger(Number(x.text)) && Number(x.text) >= min) return Number(x.text)
    if (x && ts.isIdentifier(x) && params.has(x.text) && (opts.params || what === 'permits')) return x.text
    return refuse(e ?? at, `${what} of other than a whole number${min ? ` from ${min}` : ''} written here${what === 'permits' ? ' (or a parameter of the make)' : ''}`)
  }
  for (const st of body.statements) {
    if (!ts.isVariableStatement(st)) continue
    for (const d of st.declarationList.declarations) {
      const init = d.initializer && strip(d.initializer), call = init && ts.isYieldExpression(init) && init.expression ? strip(init.expression) : init
      const a = call && ts.isCallExpression(call) ? api(call.expression) : undefined
      if (!a || !(a in QUEUES || SEMS.has(a))) continue
      const c = call as ts.CallExpression
      if (!ts.isIdentifier(d.name)) refuse(d, `${text(d)}: a ${a.split('.')[0]} bound to a pattern (one name is read)`)
      if (st.declarationList.declarations.length > 1) refuse(st, `${text(st)}: a primitive declared beside others (one declaration a statement)`)
      const name = (d.name as ts.Identifier).text, unsafe = /Unsafe|unsafe/.test(a)
      if (!unsafe && !(init && ts.isYieldExpression(init) && init.asteriskToken)) refuse(d, `${text(d)}: ${a} not yielded where the service is made`)
      if (SEMS.has(a)) { insts.push({name, kind: 'semaphore', permits: whole(c.arguments[0], 'permits', c, 0), fields: [`${name}_taken`, `${name}_held`], decl: d, stmt: st}); continue }
      let strategy = QUEUES[a]!, cap: ts.Expression | undefined = c.arguments[0]
      if (a === 'Queue.make') {
        // (4.x: make({capacity, strategy}); no capacity is an unbounded queue)
        const o = c.arguments[0] && strip(c.arguments[0])
        if (o && !ts.isObjectLiteralExpression(o)) refuse(o, 'Queue.make of other than {capacity, strategy} written here')
        const props = new Map((o as ts.ObjectLiteralExpression | undefined)?.properties.map(p => (ts.isPropertyAssignment(p) ? [memberName(p.name), p.initializer] as const : refuse(p, `Queue.make's ${text(p)} (capacity and strategy are read)`))) ?? [])
        for (const k of props.keys()) if (k !== 'capacity' && k !== 'strategy') refuse(o!, `Queue.make's ${k} (capacity and strategy are read)`)
        const sv = props.get('strategy') && strip(props.get('strategy')!)
        if (sv && !ts.isStringLiteral(sv)) refuse(sv, 'a strategy other than a string written here')
        strategy = !props.has('capacity') ? 'unbounded' : (sv as ts.StringLiteral | undefined)?.text === 'dropping' ? 'dropping' : (sv as ts.StringLiteral | undefined)?.text === 'sliding' ? 'sliding' : 'bounded'
        cap = props.get('capacity')
      }
      const capacity = strategy === 'unbounded' ? undefined : whole(cap, 'a capacity', c, 1)
      // (the item's type: the queue's first type argument)
      const t = s.checker.getTypeAtLocation(d.name), args = t.aliasTypeArguments ?? (t.flags & ts.TypeFlags.Object ? s.checker.getTypeArguments(t as ts.TypeReference) : undefined)
      const it = args?.[0] ?? refuse(d, `${name}: no type for the queue's items`)
      const written = c.typeArguments?.[0]?.getText()
      insts.push({name, kind: 'queue', strategy, ...(capacity !== undefined ? {capacity} : {}), fields: ['items', 'head', 'tail', 'open'].map(f => `${name}_${f}`), decl: d, stmt: st, item: written ?? s.checker.typeToString(it, d, ts.TypeFormatFlags.NoTruncation), zero: zeroOf(s, it, d)})
    }
  }
  if (!insts.length) return undefined
  // (the names the model gives: none of the code's own)
  // (the code's identifiers, not its comments: a law there names the model's fields)
  const ids = new Set<string>(), idsOf = (n: ts.Node): void => { if (ts.isIdentifier(n)) ids.add(n.text); ts.forEachChild(n, idsOf) }
  idsOf(sf)
  for (const i of insts) for (const n of i.fields) if (ids.has(n)) refuse(i.decl, `${n} is a name of the code's, and one the model of ${i.name} gives`)
  for (const n of ids) if (/^gdp\$/.test(n) || insts.some(i => n.startsWith(`${i.name}$`))) refuse(sf.statements[0] ?? sf, `${n}: a name of the code's like those the model of the primitives is written with (gdp$..., <primitive>$...)`)
  const ofDecl = new Map(insts.map(i => [i.decl as ts.Node, i]))
  const instOf = (x: ts.Expression | undefined): Inst | undefined => { const e = x && strip(x); const d = e && ts.isIdentifier(e) ? s.checker.getSymbolAtLocation(e)?.valueDeclaration : undefined; return d ? ofDecl.get(d) : undefined }
  // Every reference to each primitive (each the operation it is called with), seen first without refusing: a service
  // whose only primitives are Semaphores of 1 used as locks is read as before, and a queue it shuts down is known.
  const refs: [Inst, ts.Identifier][] = []
  const scan = (n: ts.Node): void => {
    if (ts.isIdentifier(n) && !(ts.isVariableDeclaration(n.parent) && n.parent.name === n)) { const i = instOf(n); if (i) refs.push([i, n]) }
    ts.forEachChild(n, scan)
  }
  scan(sf)
  const opOf = (id: ts.Identifier): string => {
    const p = id.parent
    if (ts.isCallExpression(p) && p.arguments[0] === id) return (api(p.expression) ?? '').split('.')[1] ?? ''
    return ts.isPropertyAccessExpression(p) && p.expression === id ? memberName(p.name) : ''
  }
  const isLock = (id: ts.Identifier): boolean => {
    const p = id.parent, op = opOf(id)
    if (op === 'withPermit') return true
    const n = op !== 'withPermits' ? undefined : ts.isCallExpression(p) ? p.arguments[1] : ts.isCallExpression(p.parent) ? p.parent.arguments[0] : undefined
    return !!n && ts.isNumericLiteral(strip(n)) && (strip(n) as ts.NumericLiteral).text === '1'
  }
  if (insts.every(i => i.kind === 'semaphore' && i.permits === 1) && refs.every(([, id]) => isLock(id))) return undefined
  for (const [i, id] of refs) if (i.kind === 'queue' && opOf(id) === 'shutdown') i.shuts = true

  // Every use of each primitive, an edit: an operation a call of the model's, withPermits statements of the method's.
  const edits = new Map<ts.Node, () => string>(), lock = new Set<Inst>()
  const count = (e: ts.Expression | undefined, at: ts.Node) => whole(e, 'a permit count', at, 1)
  const classify = (i: Inst, id: ts.Identifier): void => {
    const p = id.parent, gp = p.parent
    // Queue.op(q, ...), Semaphore.op(s, ...)
    if (ts.isCallExpression(p) && p.arguments[0] === id) {
      const a = api(p.expression) ?? '', [m = '', op = ''] = a.split('.')
      if (m === 'Queue' && i.kind === 'queue') return queueOp(i, op, p, p.arguments.slice(1))
      if (m === 'Semaphore' && i.kind === 'semaphore') return semOp(i, op, p, p.arguments.slice(1), true)
    }
    // q.op(...), q.op (3.x's members), s.op(...), s.op
    if (ts.isPropertyAccessExpression(p) && p.expression === id) {
      const op = memberName(p.name), call = ts.isCallExpression(gp) && gp.expression === p ? gp : undefined
      if (i.kind === 'queue') {
        if (v4) refuse(p, `${text(p)}: a queue's member (Queue.${op}(${i.name}, ...) is read)`)
        if (op === 'offer' && call) return queueOp(i, op, call, call.arguments)
        if (op === 'capacity' && call) return queueOp(i, op, call, [])
        if (op !== 'offer' && op !== 'capacity' && !call) return queueOp(i, op, p, [])
        return void refuse(p, `${text(p)} (a queue's ${QOPS3.join(', ')} are read)`)
      }
      return semOp(i, op, call ?? p, call?.arguments ?? [], false)
    }
    refuse(id, `${i.name} used other than by its operations (a ${i.kind} the make effect makes is read where its operations are called on it, not passed or kept)`)
  }
  const queueOp = (i: Inst, op: string, call: ts.Node, args: readonly ts.Expression[]): void => {
    const ops = v4 ? QOPS4 : QOPS3
    if (op === 'capacity' && !v4) { edits.set(call, () => String((i as {capacity?: number | string}).capacity ?? Number.MAX_SAFE_INTEGER)); return }
    if (!ops.includes(op)) {
      const why = !v4 && ['size', 'isEmpty', 'isFull'].includes(op) ? ': Effect 3\'s size counts the fibers waiting on the queue (takers below zero, back-pressured offers past the capacity), which the rule doesn\'t hold (a waiting request is one not yet taken)' : ''
      refuse(call, `Queue.${op}${why} (${ops.join(', ')} are read${v4 ? '' : ', and capacity'})`)
    }
    if (args.length !== (op === 'offer' ? 1 : 0)) refuse(call, `Queue.${op} with ${args.length} arguments`)
    edits.set(call, () => `${i.name}$${op}(${args.map(render).join(', ')})`)
  }
  const semOp = (i: Inst, op: string, call: ts.Node, args: readonly ts.Expression[], fn: boolean): void => {
    if (op === 'take' || op === 'release') {
      if (args.length !== 1 || !ts.isCallExpression(call)) refuse(call, `${text(call)}: ${op} of one count`)
      count(args[0], call)
      edits.set(call, () => `${i.name}$${op}(${render(args[0]!)})`)
      return
    }
    if (op === 'releaseAll') { if (fn ? args.length : ts.isCallExpression(call)) refuse(call, `${text(call)}: releaseAll is an effect`); edits.set(call, () => `${i.name}$releaseAll()`); return }
    if (op === 'withPermits' || op === 'withPermit') {
      // (the count and the effect: s.withPermits(n)(e), s.withPermit(e), Semaphore.withPermits(s, n)(e) or (s, n, e),
      // Semaphore.withPermit(s)(e) or (s, e))
      const k = op === 'withPermit' ? 1 : count(args[0], call), rest = op === 'withPermit' ? args : args.slice(1)
      let outer: ts.Node = call, eff = rest[0]
      if (!eff) { const o = call.parent; if (!ts.isCallExpression(o) || o.expression !== call || o.arguments.length !== 1) return void refuse(call, `${text(call)} other than applied to an effect here`); outer = o; eff = o.arguments[0] }
      if (rest.length > 1) refuse(call, `${text(call)} with more arguments than the effect`)
      lock.add(i)
      return withPermits(i, k as number, outer as ts.CallExpression, eff!)
    }
    refuse(call, `${text(call)} (a semaphore's take, release, releaseAll, withPermits and withPermit are read${op === 'resize' ? '; resize changes its permits, which the model holds fixed' : ''})`)
  }
  // withPermits(n)(e), yielded as a statement of a generator's body: take, e's statements (or e), release. A failure in
  // e's body releases first (withPermits releases on any exit); one e may fail with elsewhere (a helper, a transaction,
  // a queue's interrupt) is refused, since the release would be skipped.
  let tmp = 0
  const withPermits = (i: Inst, k: number, w: ts.CallExpression, eff: ts.Expression): void => {
    const y = w.parent, st = y && ts.isYieldExpression(y) && y.asteriskToken && y.expression === w ? stmtOf(y) : undefined
    if (!st) return void refuse(w, `${text(w)} other than yielded as a statement of a generator's body (\`yield* ${i.name}.withPermits(n)(...)\`, \`const x = yield* ...\` or \`return yield* ...\`): its body's steps and the release are written as the method's own steps${ts.isArrowFunction(w.parent) ? ' (write the method as Effect.fn(\'name\')(function* () { ... }))' : ''}`)
    const take = `yield* ${i.name}$take(${k}); `, release = `yield* ${i.name}$release(${k})`
    if (ts.isVariableStatement(st) && (st.declarationList.declarations.length !== 1 || !ts.isIdentifier(st.declarationList.declarations[0]!.name))) refuse(st, `${text(st)}: one name declared`)
    const into = ts.isVariableStatement(st) ? (st.declarationList.declarations[0]!.name as ts.Identifier).text : undefined
    const kw = ts.isVariableStatement(st) && !(st.declarationList.flags & ts.NodeFlags.Const) ? 'let' : 'const', r = `gdp$v${tmp++}`
    const g = genBody(eff)
    if (!g) {
      if (canFail(eff)) refuse(eff, `${text(eff)} inside withPermits may fail (or be interrupted) other than by a statement of the body written here: withPermits releases its permits on any exit, which the steps hold only for a failure written in the body (write it as Effect.gen(function* () { ... }) with the failure there)`)
      edits.set(st, () => (ts.isExpressionStatement(st) ? `${take}yield* ${render(eff)}; ${release}` : into ? `${take}${kw} ${into} = yield* ${render(eff)}; ${release}` : `${take}const ${r} = yield* ${render(eff)}; ${release}; return ${r}`))
      return
    }
    // (the body's names must not meet the method's: they are declared beside them)
    const outerNames = new Set<string>(), innerNames = new Set<string>()
    const names = (n: ts.Node, to: Set<string>) => { const go = (x: ts.Node) => { if ((ts.isVariableDeclaration(x) || ts.isParameter(x)) && ts.isIdentifier(x.name)) to.add(x.name.text); if (!ts.isFunctionLike(x)) ts.forEachChild(x, go) }; go(n) }
    for (const other of (st.parent as ts.Block).statements) if (other !== st) names(other, outerNames)
    let fnHost: ts.Node | undefined = st.parent; while (fnHost && !ts.isFunctionLike(fnHost)) fnHost = fnHost.parent
    for (const p of (fnHost as ts.FunctionLikeDeclaration | undefined)?.parameters ?? []) if (ts.isIdentifier(p.name)) outerNames.add(p.name.text)
    for (const b of g.statements) names(b, innerNames)
    for (const n of innerNames) if (outerNames.has(n)) refuse(eff, `${n} is declared inside withPermits' body and around it (the body's statements are written beside the method's: rename one)`)
    const last = g.statements.at(-1), value = last && ts.isReturnStatement(last) && !failing(last.expression) ? last : undefined
    const stmts = value ? g.statements.slice(0, -1) : g.statements
    // (each failing statement of the body releases first; every other may fail nowhere)
    const walk = (b: ts.Statement): void => {
      if ((ts.isExpressionStatement(b) || ts.isReturnStatement(b)) && failing(b.expression)) { edits.set(b, () => `{ ${release}; ${render0(b)} }`); return }
      if (ts.isReturnStatement(b)) return void refuse(b, `${text(b)}: a return inside withPermits' body before its end (the body's statements are written in the method's: return at its end)`)
      if (ts.isIfStatement(b)) { if (canFail(b.expression)) refuse(b.expression, `${text(b.expression)} inside withPermits may fail other than by a statement of its body`); walk(b.thenStatement); if (b.elseStatement) walk(b.elseStatement); return }
      if (ts.isBlock(b)) return b.statements.forEach(walk)
      if (canFail(b)) refuse(b, `${text(b)} inside withPermits may fail (or be interrupted) other than by a statement of its body written here (a helper's or a transaction's failure, an operation on a queue the service shuts down): withPermits releases its permits on any exit, which the steps hold only there`)
    }
    stmts.forEach(walk)
    if (value?.expression && canFail(value.expression)) refuse(value, `${text(value)} inside withPermits may fail other than by a statement of its body`)
    edits.set(st, () => {
      // (the body's statements with the lines between them, so the code keeps its place)
      let out = take, at = g.getStart(sf) + 1
      for (const b of stmts) { out += gap(at, b.getStart(sf)) + render(b); at = b.end }
      const v = value?.expression ? render(value.expression) : 'undefined'
      const tail = ts.isExpressionStatement(st) ? `${value?.expression && /\byield\b/.test(v) ? `${v}; ` : ''}${release}` : into ? `${kw} ${into} = ${v}; ${release}` : `const ${r} = ${v}; ${release}; return ${r}`
      return `${out}${gap(at, value ? value.getStart(sf) : g.end)} ${tail}`
    })
  }
  const gap = (a: number, b: number) => '\n'.repeat((sf.text.slice(a, Math.max(a, b)).match(/\n/g) ?? []).length) || ' '
  const failing = (e: ts.Expression | undefined): boolean => {
    const y = e && strip(e)
    if (!y || !ts.isYieldExpression(y) || !y.expression) return false
    const x = strip(y.expression)
    return ts.isNewExpression(x) || FAILS.test((ts.isCallExpression(x) ? api(x.expression) : api(x)) ?? '')
  }
  // Whether running n may fail: a failure in it, in a helper it calls, or an operation that interrupts on a queue the
  // service shuts down.
  const memo = new Map<ts.Node, boolean>()
  const canFail = (n: ts.Node): boolean => {
    let hit = false
    const go = (x: ts.Node) => {
      if (hit) return
      if (ts.isYieldExpression(x) && x.expression && ts.isNewExpression(strip(x.expression))) { hit = true; return }
      if (ts.isCallExpression(x) || ts.isPropertyAccessExpression(x)) {
        const a = api(ts.isCallExpression(x) ? x.expression : x) ?? ''
        if (FAILS.test(a)) { hit = true; return }
        const q = ts.isCallExpression(x) ? instOf(x.arguments[0]) : instOf(x.expression)
        if (q?.kind === 'queue' && q.shuts && (!v4 || a === 'Queue.take')) { hit = true; return }
      }
      if (ts.isIdentifier(x) && ts.isCallExpression(x.parent) && x.parent.expression === x) {
        const d = s.checker.getSymbolAtLocation(x)?.valueDeclaration
        if (d && ts.isVariableDeclaration(d) && d.initializer && d.getSourceFile() === sf) {
          if (!memo.has(d)) { memo.set(d, false); memo.set(d, canFail(d.initializer)) }
          if (memo.get(d)) { hit = true; return }
        }
      }
      ts.forEachChild(x, go)
    }
    go(n)
    return hit
  }
  for (const [i, id] of refs) classify(i, id)
  for (const i of insts) edits.set(i.stmt, () => model(i, v4))
  const out = `${imports(v4)}${render(sf)}`
  const notes = insts.map(i => (i.kind === 'queue'
    ? `${i.name} is an Effect ${v4 ? 4 : 3} Queue (${i.strategy}${i.capacity !== undefined ? `, ${i.capacity} items` : ''}), modelled: ${i.fields.join(', ')}; it holds the items at ${i.name}_head .. ${i.name}_tail - 1, oldest first${i.strategy === 'bounded' ? '; an offer to it full waits' : i.strategy === 'dropping' ? '; an offer to it full answers false' : i.strategy === 'sliding' ? '; an offer to it full lets its oldest item go' : ''}; a take from it empty waits${i.shuts ? `; shut down, it drops what it holds (${WAITS_FOREVER})` : ''}`
    : `${i.name} is an Effect ${v4 ? 4 : 3} Semaphore of ${i.permits} permits, modelled: ${i.name}_taken, the permits taken, and ${i.name}_held, those the calling fiber holds (its takes less its releases; under many fibers each fiber's, summing to ${i.name}_taken); a take waits until they are free, a release gives them back unchecked (as Effect does)${lock.has(i) ? '; withPermits is the take, its body\'s statements, the release (a failure in the body releasing first)' : ''}`))
  return {code: out, prims: insts.map(({decl: _d, stmt: _s, item: _i, zero: _z, shuts: _h, ...p}) => p as Prim), notes}

  // The code with every edit made: a node edited is its edit, else its text with its children's edits. (Each edit keeps
  // its lines: the code after it is where it was, so a refusal's place is the file's.)
  function render(n: ts.Node): string {
    const e = edits.get(n)
    if (!e) return render0(n)
    const out = e(), lines = n.getText(sf).split('\n').length - out.split('\n').length
    return lines > 0 ? out + '\n'.repeat(lines) : out
  }
  function render0(n: ts.Node): string {
    const start = ts.isSourceFile(n) ? 0 : n.getStart(sf)
    if (![...edits.keys()].some(k => k !== n && k.pos >= n.pos && k.end <= n.end)) return sf.text.slice(start, n.end)
    let out = '', pos = start
    for (const c of n.getChildren(sf)) {
      if (ts.isJSDoc(c)) continue
      out += sf.text.slice(pos, Math.max(pos, c.getStart(sf))) + render(c)
      pos = c.end
    }
    return out + sf.text.slice(pos, n.end)
  }
}
// The statement a yield* is the whole of: `yield* x;`, `const v = yield* x`, `return yield* x`.
function stmtOf(y: ts.YieldExpression): ts.Statement | undefined {
  let p: ts.Node = y.parent
  while (ts.isParenthesizedExpression(p)) p = p.parent
  if (ts.isExpressionStatement(p) || ts.isReturnStatement(p)) return ts.isBlock(p.parent) ? p : undefined
  if (ts.isVariableDeclaration(p) && ts.isVariableDeclarationList(p.parent) && ts.isVariableStatement(p.parent.parent) && ts.isBlock(p.parent.parent.parent)) return p.parent.parent
  return undefined
}
// Effect.gen(function* () {...})'s body.
function genBody(e: ts.Expression): ts.Block | undefined {
  const x = strip(e)
  if (!ts.isCallExpression(x) || !ts.isPropertyAccessExpression(x.expression) || memberName(x.expression.name) !== 'gen' || x.arguments.length !== 1) return undefined
  const f = strip(x.arguments[0]!)
  return ts.isFunctionExpression(f) && f.asteriskToken && ts.isBlock(f.body) ? f.body : undefined
}
// An item's zero, for the model's read at the queue's head (never read where the queue holds an item): a number's 0, a
// boolean's false. (A record's would make the read one object or another by the path, a string's a value no union holds:
// refused.)
function zeroOf(s: Setup, t: ts.Type, at: ts.Node): string {
  if (t.flags & ts.TypeFlags.NumberLike) return '0'
  if (t.flags & ts.TypeFlags.BooleanLike || (t.isUnion() && t.types.every(u => u.flags & ts.TypeFlags.BooleanLiteral))) return 'false'
  return refuse(at, `a queue of ${s.checker.typeToString(t)} (numbers and booleans are read: queue an id, the item in a Ref's map)`)
}

// --- the model -------------------------------------------------------------------------------------------------------
const imports = (v4: boolean) => (v4 ? "import {Effect as gdp$Effect, TxRef as gdp$TxRef, Option as gdp$Option} from 'effect'; " : "import {STM as gdp$STM, TRef as gdp$TRef, Option as gdp$Option} from 'effect'; ")
// The declarations a primitive is written as: its fields' TxRefs (TRefs) and one function an operation, each one
// transaction (on one line, so the code after it keeps its place).
function model(i: Inst, v4: boolean): string {
  const R = v4 ? 'gdp$TxRef' : 'gdp$TRef', tx = (b: string) => (v4 ? `gdp$Effect.tx(gdp$Effect.gen(function* () { ${b} }))` : `gdp$STM.commit(gdp$STM.gen(function* () { ${b} }))`)
  const wait = v4 ? 'return yield* gdp$Effect.txRetry' : 'return yield* gdp$STM.retry', get = (r: string) => `(yield* ${R}.get(${r}))`, set = (r: string, v: string) => `yield* ${R}.set(${r}, ${v});`
  const mk = (n: string, t: string, v: string) => `const ${n} = yield* ${R}.make<${t}>(${v});`
  const fn = (op: string, ps: string, b: string) => `const ${i.name}$${op} = (${ps}) => ${tx(b)};`
  if (i.kind === 'semaphore') {
    const n = i.name, P = String(i.permits)
    // (and the permits the calling fiber holds, its takes less its releases: the taken are every fiber's, summed)
    const own = (d: string) => `const o = ${get(`${n}_held`)}; ${set(`${n}_held`, `o + ${d}`)}`
    return [mk(`${n}_taken`, 'number', '0'), mk(`${n}_held`, 'number', '0'),
      fn('take', 'n: number', `const t = ${get(`${n}_taken`)}; if (${P} - t < n) ${wait}; ${set(`${n}_taken`, 't + n')} ${own('n')} return n`),
      fn('release', 'n: number', `const t = ${get(`${n}_taken`)}; ${set(`${n}_taken`, 't - n')} ${own('-n')} return ${P} - (t - n)`),
      fn('releaseAll', '', `const t = ${get(`${n}_taken`)}; ${set(`${n}_taken`, '0')} ${own('-t')} return ${P}`)].join(' ')
  }
  const q = i.name, A = i.item!, Z = i.zero!, C = i.capacity, closed = (v: string) => `if (!${get(`${q}_open`)}) ${v4 ? `return ${v}` : wait};`
  const full = C === undefined ? '' : `if (t - h >= ${C}) ${i.strategy === 'bounded' ? `${wait};` : i.strategy === 'dropping' ? 'return false;' : `{ ${set(`${q}_head`, 'h + 1')} }`}`
  const front = `const h = ${get(`${q}_head`)}; const t = ${get(`${q}_tail`)};`
  return [mk(`${q}_items`, `ReadonlyMap<number, ${A}>`, 'new Map()'), mk(`${q}_head`, 'number', '0'), mk(`${q}_tail`, 'number', '0'), mk(`${q}_open`, 'boolean', 'true'),
    fn('offer', `x: ${A}`, `${closed('false')} ${front} ${full} yield* ${R}.update(${q}_items, m => new Map(m).set(t, x)); ${set(`${q}_tail`, 't + 1')} return true`),
    // (4.x's take fails on a shut-down queue as 3.x's interrupts: a wait that never ends, as the notes say)
    fn('take', '', `if (!${get(`${q}_open`)}) ${wait}; ${front} if (t <= h) ${wait}; const m = ${get(`${q}_items`)}; ${set(`${q}_head`, 'h + 1')} return m.get(h) ?? ${Z}`),
    fn('poll', '', `${closed('gdp$Option.none()')} ${front} if (t <= h) return gdp$Option.none(); const m = ${get(`${q}_items`)}; ${set(`${q}_head`, 'h + 1')} return gdp$Option.some(m.get(h) ?? ${Z})`),
    fn('size', '', `${closed('0')} return ${get(`${q}_tail`)} - ${get(`${q}_head`)}`),
    fn('isFull', '', C === undefined ? 'return false' : `${closed('false')} return ${get(`${q}_tail`)} - ${get(`${q}_head`)} === ${C}`),
    fn('isShutdown', '', `return !${get(`${q}_open`)}`),
    fn('shutdown', '', `if (!${get(`${q}_open`)}) return ${v4 ? 'false' : 'undefined'}; ${set(`${q}_head`, get(`${q}_tail`))} ${set(`${q}_open`, 'false')} return ${v4 ? 'true' : 'undefined'}`)].join(' ')
}

// --- the primitives' own rules, their laws, and the real primitive beside them -----------------------------------------
// The canonical service of each (one method an operation, the capacity or the permits a parameter), read through the
// same model: its rule is the model's, so a law proven of it holds of every instance (a service's are its fields, written
// by these operations alone). primitiveConforms runs that rule beside Effect's own primitive on random operations, each
// started on a fiber of its own (some waiting, some interrupted), and compares what completes, what waits and what the
// primitive holds.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Mod = Record<string, any>
export type Spec = {kind: 'queue', strategy: Strategy} | {kind: 'semaphore'}
const QUEUE_OPS = (v4: boolean) => (v4 ? ['offer', 'take', 'poll', 'size', 'isFull', 'shutdown'] : ['offer', 'take', 'poll', 'isShutdown', 'shutdown'])
const SEM_OPS = ['take1', 'take2', 'release1', 'release2', 'releaseAll']
function canonical(spec: Spec, v4: boolean): string {
  const m = (n: string, b: string) => `  const ${n} = Effect.fn('${n}')(function* (${n === 'offer' ? 'x: number' : ''}) { ${b} })`
  if (spec.kind === 'semaphore') return `import {Effect${v4 ? ', Semaphore' : ''}} from 'effect'
export const make = (permits: number) => Effect.gen(function* () {
  const s = yield* ${v4 ? 'Semaphore.make' : 'Effect.makeSemaphore'}(permits)
${[1, 2].flatMap(n => [m(`take${n}`, `return yield* s.take(${n})`), m(`release${n}`, `return yield* s.release(${n})`)]).join('\n')}
${m('releaseAll', 'return yield* s.releaseAll')}
  return {${SEM_OPS.join(', ')}}
})
`
  const ops = QUEUE_OPS(v4), body: Record<string, string> = {
    offer: 'return yield* Queue.offer(q, x)', take: 'return yield* Queue.take(q)', size: 'return yield* Queue.size(q)', isFull: 'return yield* Queue.isFull(q)', isShutdown: 'return yield* Queue.isShutdown(q)',
    poll: 'const o = yield* Queue.poll(q); return Option.isSome(o) ? Option.getOrElse(o, () => 0) : -1', shutdown: v4 ? 'return yield* Queue.shutdown(q)' : 'yield* Queue.shutdown(q)'}
  return `import {Effect, Option, Queue} from 'effect'
export const make = (${spec.strategy === 'unbounded' ? '' : 'capacity: number'}) => Effect.gen(function* () {
  const q = yield* Queue.${spec.strategy}<number>(${spec.strategy === 'unbounded' ? '' : 'capacity'})
${ops.map(o => m(o, body[o]!)).join('\n')}
  return {${ops.join(', ')}}
})
`
}
// The canonical service's rule (an Extraction of core/effect.ts's): a queue of numbers of a strategy, every capacity (a
// natural) its parameter; a semaphore, every number of permits.
// (`file`: where the code is read as if it were, so its imports resolve to that `effect`'s types: by default beside the
// working directory)
export function primitiveRule(spec: Spec, effect: Mod, opts: {runs?: number, file?: string} = {}): Extraction {
  const v4 = 'TxRef' in effect, name = spec.kind === 'queue' ? `queue-${spec.strategy}` : 'semaphore'
  return extractEffect({code: canonical(spec, v4), file: opts.file ?? `${name}.ts`}, {entry: 'make', effect, fibers: false, capacityParam: true, domains: {capacity: 'nat', permits: 'nat'}, check: {runs: opts.runs ?? 40}} as EffectOptions)
}
// Its laws: the invariants (a queue's bound; at most the permits taken) and what each operation does to it, as step laws
// (nothing is lost: what comes in comes by an offer, at the tail; what leaves is the oldest, to the take or poll whose
// answer it is, to a slide or to a shutdown; what is held stays where it is). The semaphore's use law (never released
// past what was taken) is no law of Effect's own (a release is unchecked): it is a law of a service's use, refuted here.
export function primitiveLaws(x: Extraction, spec: Spec): {laws: Law[], stepLaws: StepLaw[], refuted: Law[]} {
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  const r = x.rule as any, inv = x.invariants ?? [], is = (b: Any, ...ms: string[]) => dsl.any(...ms.map(m => b.method.is(m)))
  if (spec.kind === 'semaphore') {
    return {laws: inv, refuted: (x as Extraction & {primitives?: {laws: Law[]}[]}).primitives?.flatMap(p => p.laws) ?? [], stepLaws: [
      r.stepLaw('a take of n waits until n are free, then takes them', (b: Any, a: Any) => dsl.any(a.s_taken.eq(b.s_taken), a.s_taken.eq(b.s_taken.plus(dsl.when(is(b, 'take2'), 2, 1))).and(a.s_taken.atMost(b.permits))), (b: Any) => is(b, 'take1', 'take2')),
      r.stepLaw('a release of n gives back n, unchecked', (b: Any, a: Any) => a.s_taken.eq(b.s_taken.minus(dsl.when(is(b, 'release2'), 2, 1))), (b: Any) => is(b, 'release1', 'release2')),
      r.stepLaw('only a take waits', (b: Any, a: Any) => a.s_taken.eq(b.s_taken).implies(is(b, 'take1', 'take2').or(b.method.is('releaseAll').and(b.s_taken.eq(0)))), (b: Any) => is(b, 'take1', 'take2', 'release1', 'release2', 'releaseAll').and(dsl.not(is(b, 'take1', 'take2')))),
    ]}
  }
  const st = spec.strategy, cap = (b: Any) => (st === 'unbounded' ? undefined : b.capacity), full = (b: Any) => (cap(b) ? b.q_tail.minus(b.q_head).atLeast(cap(b)) : dsl.no)
  const item = (s: Any, k: Any) => s.q_items.at(k).value, same = (b: Any, a: Any) => a.q_head.eq(b.q_head).and(a.q_tail.eq(b.q_tail))
  const appended = (b: Any, a: Any) => a.q_tail.eq(b.q_tail.plus(1)).and(dsl.same(item(a, b.q_tail), b.offer_x))
  return {laws: inv, refuted: [], stepLaws: [
    r.stepLaw(st === 'bounded' ? 'an offer appends its item at the tail (full, it waits)' : st === 'dropping' ? 'an offer appends its item at the tail; full, it answers false and changes nothing' : st === 'sliding' ? 'an offer appends its item at the tail; full, the oldest item leaves to make room' : 'an offer appends its item at the tail',
      (b: Any, a: Any) => dsl.any(same(b, a), appended(b, a).and(st === 'sliding' ? dsl.when(full(b), a.q_head.eq(b.q_head.plus(1)), a.q_head.eq(b.q_head)) : a.q_head.eq(b.q_head).and(dsl.not(full(b))))).and(st === 'dropping' ? full(b).implies(same(b, a)) : dsl.yes),
      (b: Any) => b.method.is('offer')),
    r.stepLaw('a take or a poll answers the oldest item, which leaves', (b: Any, a: Any) => a.q_head.eq(b.q_head).or(a.q_head.eq(b.q_head.plus(1)).and(dsl.same(dsl.when(b.method.is('take'), a.take_result, a.poll_result), item(b, b.q_head)))), (b: Any) => is(b, 'take', 'poll')),
    r.stepLaw('only the oldest item leaves, to a take, a poll, a slide or a shutdown', (b: Any, a: Any) => dsl.any(a.q_head.eq(b.q_head), a.q_head.eq(b.q_head.plus(1)).and(is(b, 'take', 'poll', ...(st === 'sliding' ? ['offer'] : []))), b.method.is('shutdown').and(a.q_head.eq(b.q_tail)))),
    r.stepLaw('nothing comes in but an offer, at the tail', (b: Any, a: Any) => a.q_tail.eq(b.q_tail).or(b.method.is('offer').and(a.q_tail.eq(b.q_tail.plus(1))))),
    r.stepLaw('the items held stay where they are', (b: Any, a: Any) => dsl.forall((k: Any) => k.atLeast(a.q_head).and(k.lt(b.q_tail)).implies(dsl.same(item(a, k), item(b, k))))),
  ]}
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
// The rule beside Effect's own primitive: `runs` runs of `depth` operations (a capacity from 1 to 4, or 0 to 3 permits),
// each started on a fiber of its own; after each, the runtime runs until nothing more moves, every operation that
// completed is a step the rule takes with its answer (in an order the rule allows), every one still waiting one the rule
// refuses, and what the primitive holds is the rule's (a queue's size, a semaphore's taken; at the end of a run, a queue's
// items in order). An operation that interrupts its fiber on a shut-down queue is one the rule refuses (WAITS_FOREVER).
// (checked: the completions stepped; blocked: the operations found waiting after an operation, each refused by the rule;
// waited: those ended by a shut-down queue; interrupted: the waiting ones interrupted)
export async function primitiveConforms(spec: Spec, effect: Mod, opts: {runs?: number, depth?: number, seed?: number, x?: Extraction, file?: string} = {}): Promise<{checked: number, waited: number, blocked: number, interrupted: number, failure?: string}> {
  const E = effect, v4 = 'TxRef' in E, x = opts.x ?? primitiveRule(spec, E, opts.file ? {file: opts.file} : {})
  if (!x.ok || !x.rule) return {checked: 0, waited: 0, blocked: 0, interrupted: 0, failure: `the rule: ${x.refusals.map(f => f.what).join('; ')}`}
  const r = x.rule, g = r.compiled(), interp = interpret(r.machine), rand = searchSeeded(opts.seed ?? 1)
  const inputs = (r as never as {parts: {inputs: [string, unknown][]}}).parts.inputs.map(([n]) => n).filter(n => n !== 'method')
  const ops = spec.kind === 'queue' ? QUEUE_OPS(v4) : SEM_OPS
  const tick = () => new Promise(res => setTimeout(res, 0))
  let checked = 0, waited = 0, blocked = 0, interrupted = 0
  for (let run = 0; run < (opts.runs ?? 100); run++) {
    const n = spec.kind === 'queue' ? 1 + rand(4) : rand(4), params = spec.kind === 'queue' ? (spec.strategy === 'unbounded' ? {} : {capacity: n}) : {permits: n}
    const ps = r.encodeParams(params as never)
    const prim = E.Effect.runSync(spec.kind === 'semaphore' ? (v4 ? E.Semaphore.make(n) : E.Effect.makeSemaphore(n)) : spec.strategy === 'unbounded' ? E.Queue.unbounded() : E.Queue[spec.strategy](n))
    const effOf = (op: string, arg: number): unknown => {
      if (spec.kind === 'semaphore') return op === 'releaseAll' ? prim.releaseAll : prim[op.slice(0, -1)](Number(op.slice(-1)))
      if (op === 'offer') return E.Queue.offer(prim, arg)
      if (op === 'poll') return E.Effect.map(E.Queue.poll(prim), (o: Mod) => (E.Option.isSome(o) ? o.value : -1))
      return E.Queue[op](prim)
    }
    type Op = {id: number, op: string, arg: number, fiber: Mod, exit?: Mod, at?: number, killed?: boolean}
    const live: Op[] = [], sent: string[] = [], done: Op[] = []
    let st = g.init(ps), order = 0
    const request = (o: Op) => r.encodeInput({method: o.op, ...Object.fromEntries(inputs.map(i => [i, 0])), ...(o.op === 'offer' ? {offer_x: o.arg} : {})} as never, params as never)
    const takes = (s: unknown, o: Op) => { try { return allowed(r.machine, interp, ps, s as never, request(o)) } catch { return false } }
    const at = () => `${JSON.stringify(params)}, after ${sent.join(', ')}`
    const fail = (what: string) => ({checked, waited, blocked, interrupted, failure: `${at()}: ${what}`})
    for (let d = 0; d < (opts.depth ?? 16); d++) {
      // (an operation, or now and then a waiting one interrupted, or a queue shut down)
      const pick = rand(12)
      if (pick === 0 && live.length) {
        const o = live[rand(live.length)]!
        o.killed = true; sent.push(`interrupt #${o.id}`); interrupted++
        E.Effect.runFork(E.Fiber.interrupt(o.fiber))
      } else {
        const op = ops.filter(o => o !== 'shutdown' || pick === 1)[rand(ops.length - (ops.includes('shutdown') && pick !== 1 ? 1 : 0))]!, arg = rand(10)
        const o: Op = {id: d, op, arg, fiber: undefined as never}
        sent.push(`#${d} ${op}${op === 'offer' ? `(${arg})` : ''}`)
        o.fiber = E.Effect.runFork(effOf(op, arg))
        o.fiber.addObserver((exit: Mod) => { o.exit = exit; o.at = order++ })
        live.push(o)
      }
      for (let i = 0; i < 4; i++) await tick()
      // (what completed since, in the order it did; each a step the rule takes, in some order it allows)
      const now = live.filter(o => o.exit).sort((a, b) => a.at! - b.at!)
      for (const o of now) live.splice(live.indexOf(o), 1)
      const pending = now.filter(o => !o.killed)
      for (const o of [...pending]) if (!E.Exit.isSuccess(o.exit!)) {
        // (an operation on a shut-down queue that interrupts its fiber: one the rule refuses, as a wait)
        if (takes(st, o)) return fail(`#${o.id} ${o.op} ends its fiber (${String(E.Cause.pretty(o.exit!.cause)).split('\n')[0]}), the rule takes it`)
        pending.splice(pending.indexOf(o), 1); waited++
      }
      while (pending.length) {
        const i = pending.findIndex(o => {
          if (!takes(st, o)) return false
          const s2 = g.step(ps, g.fork(st), request(o)), want = (r.decode(s2) as Record<string, unknown>)[`${o.op}_result`], got = o.exit!.value
          return typeof got === 'object' || got === undefined || JSON.stringify(want) === JSON.stringify(typeof got === 'boolean' ? got : got)
        })
        if (i < 0) {
          const o = pending[0]!, s2 = takes(st, o) ? r.decode(g.step(ps, g.fork(st), request(o))) as Record<string, unknown> : undefined
          return fail(`#${o.id} ${o.op} completes with ${JSON.stringify(o.exit!.value)}, the rule ${s2 ? `answers ${JSON.stringify(s2[`${o.op}_result`])}` : 'refuses it (it would wait)'}`)
        }
        const o = pending.splice(i, 1)[0]!
        st = g.step(ps, st, request(o)); done.push(o); checked++
      }
      // (what still waits, the rule refuses; what the primitive holds, the rule holds)
      for (const o of live) { if (!o.killed && takes(st, o)) return fail(`#${o.id} ${o.op} waits, the rule takes it`); if (!o.killed) blocked++ }
      const mine = r.decode(st) as Record<string, number | boolean>
      if (spec.kind === 'semaphore') { if (prim.taken !== mine.s_taken) return fail(`the semaphore has ${prim.taken} taken, the rule ${mine.s_taken}`) }
      else {
        const open = v4 ? prim.state._tag !== 'Done' : !prim.shutdownFlag.current
        const size = v4 ? E.Queue.sizeUnsafe(prim) : open ? prim.queue.length() : 0
        if (open !== (mine.q_open ?? true)) return fail(`the queue is ${open ? 'open' : 'shut down'}, the rule's ${open ? 'shut down' : 'open'}`)
        if (open && size !== Number(mine.q_tail) - Number(mine.q_head)) return fail(`the queue holds ${size}, the rule ${Number(mine.q_tail) - Number(mine.q_head)}`)
      }
    }
    // (the end of a run: every waiting fiber interrupted; a queue's items, polled one by one, are the rule's in order)
    for (const o of live) E.Effect.runFork(E.Fiber.interrupt(o.fiber))
    for (let i = 0; i < 4; i++) await tick()
    if (spec.kind === 'queue') {
      const mine = r.decode(st) as Record<string, unknown>, open = v4 ? prim.state._tag !== 'Done' : !prim.shutdownFlag.current
      if (open) {
        const items = (mine.q_items as Map<number, {value: number}> | Record<string, {value: number}>), held: number[] = [], got: number[] = []
        for (let k = Number(mine.q_head); k < Number(mine.q_tail); k++) held.push(Number((items instanceof Map ? items.get(k) : items[k])?.value))
        for (let k = 0; k < 64; k++) { const o = E.Effect.runSync(E.Queue.poll(prim)); if (!E.Option.isSome(o)) break; got.push(o.value) }
        if (JSON.stringify(held) !== JSON.stringify(got)) return fail(`the queue holds ${JSON.stringify(got)}, the rule ${JSON.stringify(held)}`)
      }
    }
  }
  return {checked, waited, blocked, interrupted}
}
