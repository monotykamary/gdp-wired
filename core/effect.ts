// Effect (the `effect` package, 3.x and 4.x) as a front end (`gdp-wired/effect`): a service whose make effect creates
// Refs and returns an object of methods, read as core/extract.ts reads a factory's object of functions
// (core/extract-shapes.ts). Each Ref (Ref, SynchronizedRef, SubscriptionRef, 4.x's TxRef) is a field of the state, each
// method an event, its success value `<method>_result`, a failure (Effect.fail, Effect.die, `yield* new E(...)`) the
// step's refusal, Clock.currentTimeMillis an input, a Semaphore of 1's withPermits(1) a lock; each method is one step
// (true where calls don't interleave). What is read and refused, with the reasons, is in
// skills/gdp-wired/references/writing-rules.md ("Effect services") and research/effect/README.md.
//
//   const x = extractEffect('./limiter.ts')   // a path or a URL; the service inferred; effect from the file's project
//   proveRule(x.rule!, [x.rule!.law('never below zero', ({tokens}) => tokens.atLeast(0))])
//
// {entry: 'make'} names the service, {effect} gives the module, {code, file} reads code in memory; the code-first form,
// extractEffect(code, {file, entry, effect}), stays. The check runs the code on that Effect: the service made, and each request run, by Effect.runSyncExit with a
// Clock fixed at the request's time (4.x's TestClock.setTime yields to its scheduler, which runSync can't), every Ref
// read after it. `conforms(rule, service)` runs a rule written by hand beside a running service; `fromSchema(schema)` is
// a Schema's kind.
import ts from 'typescript'
import * as dsl from './dsl.ts'
import type {Kind, Rule} from './dsl.ts'
import {type Rand, interpret, seeded} from './machine.ts'
import {allowed} from './watch.ts'
import * as I from './extract-ir.ts'
import {type Exec, type Path, Refusal, type Setup, type Source, type V, bare as strip, beside, impure, memberName, placed, refuse, shapeOf, sourceOf, text, where} from './extract-read.ts'
import {type FactoryOf, readFactory, setupOf} from './extract-shapes.ts'
import {type ExtractOptions, type Extraction, fromModel, namesOf} from './extract.ts'
import {check, sandbox} from './extract-check.ts'
import {Parts, type ScheduleRule, readSchedule, replaySchedule, scheduleConforms, scheduleRule} from './effect-schedule.ts'
import {asRule, lift} from './system.ts'
export {proveRule, proveSteps} from './dsl.ts'
export {jitterRun, replaySchedule, scheduleConforms, stepper} from './effect-schedule.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Mod = Record<string, any>
export type EffectOptions = Omit<ExtractOptions, 'entry'> & {
  // The service: its make effect's name (`make`, a Layer, an Effect.Service class, `Tag.make`); by default the one the
  // file has.
  entry?: string,
  // The `effect` package the code is written for: the check runs the code on it. By default the one the file imports
  // (its project's node_modules).
  effect?: Mod,
  // Other modules the code imports, for the check (by their specifier).
  modules?: Record<string, unknown>,
  // Calls from many fibers at once: a method that runs several transactions (or Ref operations) is one step per
  // transaction, the fibers interleaving them (core/system.ts's lift: each fiber's place and locals its own, the Refs
  // shared). By default on where the service uses transactions (STM, TRef, TxRef, Effect.tx) and a method spans several.
  fibers?: boolean,
}
const REFS = new Set(['Ref', 'SynchronizedRef', 'SubscriptionRef', 'TxRef', 'TRef']), MAKES = ['make', 'makeUnsafe', 'unsafeMake']
const STM = (api: string) => `${api} (of STM: gen, commit, succeed, sync, void, fail, die, check and retry are read)`, MATCH = (x: string) => `${x}: a matcher (write the dispatch as a switch on _tag, or ifs)`
// The Effect line the file is read for (4.x unless the project's effect is 3.x), and the policies its methods retry or
// repeat with, each read into its schedule's rule.
let V4 = true
export type MethodSchedule = {at: string, use: 'retry' | 'repeat', source: string, rule: ScheduleRule}
let found: MethodSchedule[] = []
const SLEPT = '$slept'
// Where on a path the step has changed a Ref so far (a condition in the heap, so merges and helpers carry it).
const CHANGED = '$changed'
const changedOn = (p: Path, k = CHANGED): I.B => { const o = p.heap.get(k); return o?.k === 'alias' && o.to.t === 'bool' ? o.to.e : I.F }
// Inside a transaction (STM.gen, STM.commit, 4.x's Effect.tx), the writes made before it: what a failure there keeps
// (the transaction's own are rolled back).
const OUTER = '$outer', flagged = (b: I.B) => ({k: 'alias', to: {t: 'bool', e: b}}) as never
const changedOf = (v: V, c: V): I.B => (v.t === 'phi' ? I.bite(v.c, changedOf(v.a, c), changedOf(v.b, c)) : v.t === 'ref' && c.t === 'ref' && v.id === c.id ? I.F
  : (v.t === 'num' || v.t === 'bool' || v.t === 'str' || v.t === 'choice') && v.t === c.t && I.same(v.e as never, (c as unknown as {e: never}).e) ? I.F : I.T)

// --- the reader -----------------------------------------------------------------------------------------------------
// The module of Effect a name is (Ref for `import * as Ref from 'effect/Ref'`, `import {Ref} from 'effect'`, or `E.Ref`
// of `import * as E from 'effect'`), with the member read of it: 'Ref.get'.
function apiOf(s: Setup, e: ts.Expression): string | undefined {
  e = strip(e)
  if (!ts.isPropertyAccessExpression(e)) return undefined
  const mod = (x: ts.Expression): string | undefined => {
    x = strip(x)
    if (ts.isPropertyAccessExpression(x)) return mod(x.expression) === '' ? memberName(x.name) : undefined
    let d: ts.Node | undefined = ts.isIdentifier(x) ? s.checker.getSymbolAtLocation(x)?.declarations?.[0] : undefined
    const spec = (() => { let n = d; while (n && !ts.isImportDeclaration(n)) n = n.parent; return n && ts.isStringLiteral(n.moduleSpecifier) ? n.moduleSpecifier.text : undefined })()
    if (d && ts.isNamespaceImport(d)) return spec === 'effect' ? '' : spec?.match(/^effect\/(\w+)$/)?.[1]
    return d && ts.isImportSpecifier(d) && spec === 'effect' ? (d = d.propertyName ?? d.name, (d as ts.Identifier).text) : undefined
  }
  const m = mod(e.expression)
  return m ? `${m}.${memberName(e.name)}` : undefined
}
const callOf = (s: Setup, e: ts.Expression) => (e = strip(e), ts.isCallExpression(e) ? apiOf(s, e.expression) : undefined)
// A function a service writes: Effect.fn('name')(function* ...), Effect.fn(function* ...), Effect.fnUntraced(...), an
// arrow or a function.
function fnOf(s: Setup, e: ts.Expression): ts.FunctionLikeDeclaration | undefined {
  e = strip(e)
  if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) return e
  const head = ts.isCallExpression(e) ? (ts.isCallExpression(e.expression) ? callOf(s, e.expression) : apiOf(s, e.expression)) : undefined
  if (!ts.isCallExpression(e) || (head !== 'Effect.fn' && head !== 'Effect.fnUntraced')) return undefined
  const g = e.arguments[0] && strip(e.arguments[0])
  if (!g || !ts.isFunctionExpression(g) || !g.asteriskToken) return undefined
  if (e.arguments.length > 1) refuse(e.arguments[1]!, `${head} with combinators after its body (their effects aren't read)`)
  return g
}
const genOf = (s: Setup, e: ts.Expression, which = 'Effect.gen'): ts.FunctionExpression | undefined => {
  if (callOf(s, e) !== which) return undefined
  const args = (strip(e) as ts.CallExpression).arguments, g = args.at(-1)
  if (args.length !== 1) refuse(e, `${which} with a this (a generator of one function is read)`)
  return g && ts.isFunctionExpression(g) && g.asteriskToken ? g : refuse(e, `${which} of other than a function*`)
}
// A type's type argument: Ref<A>'s A, Effect<A, E, R>'s A, Generator<Y, R, N>'s R.
const argOf = (s: Setup, t: ts.Type, i: number): ts.Type | undefined => (t.aliasTypeArguments ?? (t.flags & ts.TypeFlags.Object ? s.checker.getTypeArguments(t as ts.TypeReference) : undefined))?.[i]
const lastReturn = (b: ts.Node | undefined) => { const st = b && ts.isBlock(b) ? b.statements.at(-1) : undefined; return st && ts.isReturnStatement(st) ? st.expression : b && !ts.isBlock(b) ? b as ts.Expression : undefined }

// The service's make: the generator whose statements make the Refs and return the object, its params, and how the check
// makes the service (by calling the entry, or the effect captured where it is written).
function factoryOf(s: Setup, entry: string): FactoryOf {
  const [name, member] = entry.split('.'), NO = 'no make effect (an Effect.gen, a function returning one, Effect.fn, or Layer.effect of one)'
  let decl: ts.Node | undefined
  for (const st of s.sf.statements) {
    if ((ts.isFunctionDeclaration(st) || ts.isClassDeclaration(st)) && st.name?.text === name) decl = st
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === name) decl = d
  }
  if (!decl) return refuse(s.sf.statements[0] ?? s.sf, `no ${name} in the file`)
  // The make effect as written (a class's option or static member, a variable's value), through Layer.effect and names.
  let e: ts.Expression | undefined, at: ts.Node = decl
  if (ts.isClassDeclaration(decl)) {
    const opts = member ? undefined : decl.heritageClauses?.[0]?.types[0]?.expression, o = opts && ts.isCallExpression(opts) && opts.arguments[1] ? strip(opts.arguments[1]) : undefined
    const prop = member ? decl.members.find(x => ts.isPropertyDeclaration(x) && memberName(x.name) === member) : o && ts.isObjectLiteralExpression(o) ? o.properties.find(p => ts.isPropertyAssignment(p) && ['make', 'effect', 'scoped'].includes(memberName(p.name))) : undefined
    e = (prop as ts.PropertyDeclaration | ts.PropertyAssignment | undefined)?.initializer
  } else if (ts.isVariableDeclaration(decl)) e = decl.initializer
  else if (ts.isFunctionDeclaration(decl)) return fromFunction(decl)
  for (let i = 0; e && i < 8; i++) {
    e = strip(e)
    const api = callOf(s, e), d = ts.isIdentifier(e) ? s.checker.getSymbolAtLocation(e)?.valueDeclaration : undefined
    if ((api === 'Layer.effect' || api === 'Layer.scoped') && ts.isCallExpression(e)) e = e.arguments[1]
    else if (d && ts.isVariableDeclaration(d) && d.getSourceFile() === s.sf) { e = d.initializer; at = d } else break
  }
  if (!e) return refuse(at, `${entry}: ${NO}`)
  const gen = genOf(s, e), f = gen ? undefined : fnOf(s, e)
  if (gen) return made(gen, [], e)
  if (f && ts.isFunctionExpression(f) && f.asteriskToken) return made(f, f.parameters)
  return f ? fromFunction(f) : refuse(e, `${entry}: ${text(e)} is ${NO.replace('no make effect', 'no make effect the reader reads')}`)

  function fromFunction(f: ts.FunctionLikeDeclaration): FactoryOf {
    const r = lastReturn(f.body), g = r && genOf(s, r)
    if (!g || (ts.isBlock(f.body!) && f.body.statements.length > 1)) return refuse(f, `${entry} returns no Effect.gen (a function whose body is the make effect is read)`)
    return made(g, f.parameters)
  }
  // The make effect at `capture` (a value, not a function): captured where the code makes it, so the check runs it.
  function made(fn: ts.FunctionExpression, params: readonly ts.ParameterDeclaration[], capture?: ts.Expression): FactoryOf {
    let o = lastReturn(fn.body) && strip(lastReturn(fn.body)!)
    if (o && ts.isCallExpression(o) && ts.isPropertyAccessExpression(o.expression) && memberName(o.expression.name) === 'of' && o.arguments.length === 1) o = strip(o.arguments[0]!)
    if (!o || !ts.isObjectLiteralExpression(o)) return refuse(fn, `${entry}'s make effect returns no object of methods (\`return {...}\` or \`return Tag.of({...})\`)`)
    const refs = new Map<string, string>(), locks = new Set<ts.Node>(), effects = new Map<ts.Node, ts.Expression>()
    s.effect = hook(s, refs, locks, effects)
    s.notes.add(`${entry} is an Effect service: its state is its Refs, each method an event, a failure the step's refusal; each method is one step, which holds where calls don't interleave (one at a time, or under a Semaphore of 1)`)
    const R = 'require("gdp-wired:effect")', run = (f: string) => `{ const f = ${f}; return __R.run(typeof f === 'function' ? f(...args) : f, __now()) }`
    return {
      fn, params, obj: o,
      decl: d => {
        const init = d.initializer && strip(d.initializer), id = (d.name as ts.Identifier).text
        if (!init) return undefined
        if (fnOf(s, init)) return 'helper'
        const call = ts.isYieldExpression(init) && init.expression ? strip(init.expression) : init, api = callOf(s, call) ?? '', [m = '', op = ''] = api.split('.')
        if (REFS.has(m) && MAKES.includes(op)) {
          const start = (call as ts.CallExpression).arguments[0] ?? refuse(call, `${api}() with no start`)
          const t = argOf(s, s.checker.getTypeAtLocation(d.name), 0) ?? refuse(d, `${text(d)}: no type for the Ref's value`)
          refs.set(id, m)
          return {shape: shapeOf(t, s.checker, d), init: start}
        }
        if (m === 'STM') return refuse(d, STM(api))
        if (m === 'Semaphore' || /^Effect\.(unsafeM|m)akeSemaphore$/.test(api)) {
          const n = (call as ts.CallExpression).arguments[0]
          if (!n || !ts.isNumericLiteral(n) || n.text !== '1') return refuse(d, `${text(d)}: a Semaphore of other than 1 permit (one of 1 is read as a lock)`)
          locks.add(d); return 'helper'
        }
        if (ts.isYieldExpression(init)) return refuse(d, `${id}: ${text(init)} run while the service is made (its value comes from outside the Refs read)`)
        // An effect the service keeps (`const next = Ref.modify(...)`): made again, and run, where a method yields it.
        if (s.checker.getTypeAtLocation(d.name).getSymbol()?.getName() === 'Effect') { effects.set(d, init); return 'helper' }
        return undefined
      },
      fnOf: x => fnOf(s, x),
      result: f => { const t = s.checker.getReturnTypeOfSignature(s.checker.getSignatureFromDeclaration(f)!); return argOf(s, t, f.asteriskToken ? 1 : 0) ?? refuse(f, `${text(f)}: no type for its result (${s.checker.typeToString(t)})`) },
      run: (_, v, at2, p) => (v.t === 'eff' ? v.run(p) : refuse(at2, `${text(at2)} returns a ${v.t} where a method returns an effect`)),
      get: n => (refs.has(n) ? `${n}: ${R}.get(${JSON.stringify(refs.get(n))}, ${n})` : undefined),
      set: n => (refs.has(n) ? `${R}.set(${JSON.stringify(refs.get(n))}, ${n}, __s.${n});` : undefined),
      calls: `const __R = ${R}; __gdp.$new = function (...args) ${run(capture ? 'globalThis.__gdpMake' : `__gdp[${JSON.stringify(entry)}]`)}; __gdp.$method = function (name, args) ${run('this[name]')}; __gdp.$get = function () { return this.__gdpGet() }; __gdp.$at = function (fields, args) { const o = __gdp.$new(...args); o.__gdpSet(fields); return o }`,
      ...(capture ? {extra: [[capture.getStart(), '(globalThis.__gdpMake = '], [capture.end, ')']] as [number, string][]} : {}),
      start: [[CHANGED, {k: 'alias', to: {t: 'bool', e: I.F}}]],
    }
  }
}

// Effect's expressions in a step: yield* runs an effect; Ref's, Effect's and Clock's calls make one (an `eff` value, run
// where it is yielded, so a helper or a branch may make it and another place run it).
const LOGS = new Set(['log', 'logTrace', 'logDebug', 'logInfo', 'logWarning', 'logError', 'logFatal', 'annotateCurrentSpan']), FAILS = new Set(['fail', 'failSync', 'die', 'dieMessage'])
const ANNOTATIONS = new Set(['Effect.withSpan', 'Effect.withLogSpan', 'Effect.annotateLogs', 'Effect.annotateSpans'])
// What a Ref operation answers: the value before, the value after, or nothing; and whether it takes a value or a function.
const ANSWERS: Record<string, 'old' | 'new' | 'none'> = {get: 'old', set: 'none', getAndSet: 'old', setAndGet: 'new', update: 'none', updateAndGet: 'new', getAndUpdate: 'old', modify: 'none'}
function hook(s: Setup, refs: Map<string, string>, locks: Set<ts.Node>, effects: Map<ts.Node, ts.Expression>) {
  const eff = (run: (p: Path) => [V, Path]): V => ({t: 'eff', run}), undef: V = {t: 'undef'}
  const lockOf = (x: ts.Expression | undefined) => { const d = x && ts.isIdentifier(x) ? s.checker.getSymbolAtLocation(x)?.valueDeclaration : undefined; return !!d && locks.has(d) }
  // An error made of pure values: `new E({...})` of a class (an error class has no effects), or a plain value.
  const effectful = (x: ts.Expression) => (x = strip(x), ts.isNewExpression(x) && ts.isIdentifier(x.expression) ? (x.arguments ?? []).some(impure) : impure(x))
  // A failure: the step refused where it is reached; where a Ref has been changed on the path, the Ref keeps it.
  const fail = (ex: Exec, at: ts.Node, q: Path, when: I.B = I.T): [V, Path] => {
    const kept = q.heap.has(OUTER) ? changedOn(q, OUTER) : changedOn(q), at2 = {...q, pc: [...q.pc, when]}
    if (!ex.known(at2, I.not(kept))) refuse(at, `fails after writing ${q.wrote.join(', ')}${q.heap.has(OUTER) ? ' before the transaction' : ''}: a Ref keeps what was written (a rule's refusal leaves the state as it was)`)
    ex.throws.push({pc: at2.pc})
    return [undef, {...q, pc: [...q.pc, I.not(when)]}]
  }
  // A transaction: its writes kept where it succeeds, rolled back where it fails or waits (one inside another joins it).
  const tx = (inner: V, at: ts.Node): V => (inner.t !== 'eff' ? refuse(at, `${text(at)}: a transaction of other than an effect`) : eff(q => {
    if (q.heap.has(OUTER)) return inner.run(q)
    const [v, q2] = inner.run({...q, heap: new Map(q.heap).set(OUTER, flagged(changedOn(q))).set(CHANGED, flagged(I.F))})
    const heap = new Map(q2.heap).set(CHANGED, flagged(I.or(changedOn(q2, OUTER), changedOn(q2))))
    heap.delete(OUTER)
    return [v, {...q2, heap}]
  }))
  // A transaction that waits (STM.check of false, STM.retry, 4.x's Effect.txRetry): the request isn't taken until a TRef it
  // read changes, a refusal in the rule.
  const waits = (ex: Exec, at: ts.Node, q: Path, when: I.B = I.T): [V, Path] => {
    if (!q.heap.has(OUTER)) refuse(at, `${text(at)} outside a transaction`)
    s.notes.add('a transaction that waits (STM.check, STM.retry, Effect.txRetry) is not taken until a TRef it read changes: the rule refuses the request (it is taken later as a new one)')
    return fail(ex, at, q, when)
  }
  // A function's body run on a path, with the locals where it was made.
  const body = (ex: Exec, f: ts.FunctionLikeDeclaration, at: ts.Node, locals: Map<string, V>, args: V[] = []) => eff(q => ex.inline({decl: f}, args, at, q, locals))
  return (ex: Exec, e: ts.Expression, p: Path): [V, Path] | undefined => {
    if (ts.isYieldExpression(e)) {
      if (!e.asteriskToken || !e.expression) return refuse(e, 'yield without * (Effect.gen runs an effect with yield*)')
      const x = strip(e.expression)
      // A yielded error (Schema.TaggedError, Data.TaggedError): its failure.
      if (ts.isNewExpression(x)) return effectful(x) ? refuse(x, `${text(x)}: an error made with effects`) : fail(ex, x, p)
      const [v, q] = ex.ev(x, p)
      return v.t === 'eff' ? v.run(q) : refuse(x, `yield* of ${text(x)}, not an effect the reader runs (a ${v.t})`)
    }
    if (ts.isIdentifier(e)) {
      const d = s.checker.getSymbolAtLocation(e)?.valueDeclaration, init = d && effects.get(d)
      if (!init) return undefined
      const [v, q] = ex.ev(init, {...p, locals: new Map()})
      return [v, {...q, locals: p.locals}]
    }
    if (ts.isPropertyAccessExpression(e)) {
      const api = apiOf(s, e)
      if (api === 'Effect.void' || api === 'Effect.unit' || api === 'STM.void' || api === 'STM.unit') return [eff(q => [undef, q]), p]
      if (api === 'Effect.txRetry' || api === 'STM.retry') return [eff(q => waits(ex, e, q)), p]
      if (api === 'Effect.yieldNow') return [eff(q => [undef, q]), p]
      if (api === 'Clock.currentTimeMillis') return [eff(q => (q.heap.has(SLEPT) ? refuse(e, 'the clock read after a repeat that waits (the time has moved on by its delays)') : ex.now(e, q))), p]
      if (api?.startsWith('Clock.')) return refuse(e, `${api} (Clock.currentTimeMillis is read, as an input)`)
      if (api && /^(Random|DateTime|Crypto|Console|Config|FileSystem)\./.test(api) && ts.isYieldExpression(e.parent)) return refuse(e, `${api}: an answer from outside the Refs read (Clock.currentTimeMillis is the one read, as an input)`)
      return undefined
    }
    if (!ts.isCallExpression(e)) return undefined
    const callee = strip(e.expression), api = apiOf(s, callee), [m = '', op = ''] = api?.split('.') ?? [], one = e.arguments[0]
    // A lock: sem.withPermit(effect), sem.withPermits(1)(effect), Semaphore.withPermits(sem, 1)(effect).
    if (ts.isPropertyAccessExpression(callee) && memberName(callee.name) === 'withPermit' && lockOf(callee.expression) && e.arguments.length === 1) return ex.ev(one!, p)
    if (ts.isCallExpression(callee) && e.arguments.length === 1) {
      const inner = strip(callee.expression), n = callee.arguments.at(-1)
      const sem = ts.isPropertyAccessExpression(inner) && memberName(inner.name) === 'withPermits' ? (lockOf(inner.expression) ? inner.expression : apiOf(s, inner) === 'Semaphore.withPermits' ? callee.arguments[0] : undefined) : undefined
      if (lockOf(sem)) return n && ts.isNumericLiteral(n) && n.text === '1' ? ex.ev(one!, p) : refuse(e, 'withPermits of other than 1 (a Semaphore of 1 is a lock; more permits let calls interleave)')
    }
    // x.pipe(...): only annotations (a span, a log annotation) are read through.
    if (ts.isPropertyAccessExpression(callee) && memberName(callee.name) === 'pipe' && !api) {
      const head = strip(callee.expression)
      if (e.arguments.length === 1 && apiOf(s, e.arguments[0]!) === 'STM.commit') { const [v, q] = ex.ev(head, p); return [tx(v, head), q] }
      if (callOf(s, head)?.startsWith('Match.')) return refuse(head, MATCH(text(head)))
      let [v, q] = ex.ev(callee.expression, p)
      for (const a of e.arguments) {
        const c = callOf(s, a) ?? ''
        if (ANNOTATIONS.has(c)) continue
        if ((c === 'Effect.retry' || c === 'Effect.repeat') && (strip(a) as ts.CallExpression).arguments.length === 1) { v = scheduled(ex, c, v, (strip(a) as ts.CallExpression).arguments[0]!, e); continue }
        return refuse(a, `${text(a)} in a pipe (a combinator's effect isn't read: write the step in Effect.gen)`)
      }
      return [v, q]
    }
    // A helper of the same files written with Effect.fn: its body run where it is yielded.
    if (ts.isIdentifier(callee)) {
      const d = s.checker.getSymbolAtLocation(callee)?.valueDeclaration
      const f = d && ts.isVariableDeclaration(d) && d.initializer && s.ours(d.getSourceFile()) ? fnOf(s, d.initializer) : undefined
      if (!f?.asteriskToken) return undefined
      const [args, q] = ex.args(e.arguments, p)
      return [body(ex, f, e, new Map(), args), q]
    }
    if (REFS.has(m)) return refOp(ex, e, m, op, p)
    if ((api === 'Effect.retry' || api === 'Effect.repeat') && e.arguments.length === 2) { const [v, q] = ex.ev(one!, p); return [scheduled(ex, api, v, e.arguments[1]!, e), q] }
    if (api === 'Effect.tx' || api === 'STM.commit') { const [v, q] = ex.ev(one ?? refuse(e, `${api}()`), p); return [tx(v, e), q] }
    if (m === 'STM') {
      if (op === 'gen') return [tx(body(ex, genOf(s, e, 'STM.gen')!, e, p.locals), e), p]
      if (op === 'check') {
        const f = one && fnOf(s, one)
        if (!f || f.parameters.length || ts.isBlock(f.body!)) return refuse(e, 'STM.check of other than () => condition written here')
        return [eff(q => { const [c, q1] = ex.ev(f.body as ts.Expression, q); return c.t === 'bool' ? waits(ex, e, q1, I.not(c.e)) : refuse(e, `STM.check of other than a condition (${c.t})`) }), p]
      }
      if (!['succeed', 'sync', 'fail', 'failSync', 'die', 'dieMessage'].includes(op)) return refuse(e, STM(api!))
    }
    if (m === 'Effect' || m === 'STM') {
      if (op === 'gen') return [body(ex, genOf(s, e)!, e, p.locals), p]
      if (op === 'succeed') { const [v, q] = ex.ev(one ?? refuse(e, 'Effect.succeed()'), p); return [eff(r => [v, r]), q] }
      if (op === 'sync') return [body(ex, fnOf(s, one ?? refuse(e, 'Effect.sync()')) ?? refuse(e, 'Effect.sync of other than a function written here'), e, p.locals), p]
      if (FAILS.has(op)) return e.arguments.some(effectful) ? refuse(e, `Effect.${op} of a value that has effects`) : [eff(q => fail(ex, e, q)), p]
      if (op === 'sleep') {
        if (e.arguments.some(impure)) return refuse(e, 'Effect.sleep of a value that has effects')
        return [eff(q => [undef, {...q, heap: new Map(q.heap).set(SLEPT, flagged(I.T))}]), p]
      }
      if (LOGS.has(op)) {
        if (e.arguments.some(impure)) return refuse(e, `Effect.${op} of values that have effects`)
        s.notes.add('Effect.log and span annotations are left out (they write nothing the rule keeps)')
        return [eff(q => [undef, q]), p]
      }
      if (m === 'STM') return refuse(e, STM(api!))
      return refuse(e, op === 'fn' || op === 'fnUntraced' ? `Effect.${op} as a value inside a step (a method or a helper of the service is read)` : `Effect.${op} (Effect.gen, Effect.fn bodies, succeed, sync, fail, die, void and log are read; the effect of ${op} isn't)`)
    }
    if (m === 'Match') return refuse(e, MATCH(api!))
    if (m === 'TRef') return refuse(e, `${api} (a TRef the service's make effect makes is read: get, set, update, modify and their variants)`)
    if (m === 'Semaphore') return refuse(e, `${api} (a Semaphore of 1 made by the service, as a lock, is read)`)
    return undefined
  }
  // Effect.retry / Effect.repeat of an effect read here, with a schedule (or {times, schedule, while, until}). The
  // policy is read into its schedule's rule (its laws proven on their own: x.schedules). The effect is what the service
  // does to its Refs, so each attempt of a retry fails as the first did (a failure leaves the Refs as they were, and the
  // attempts read nothing else that moves): the step is the effect's, the policy's delays passing only on the way to the
  // failure. A repeat runs it again as many times as the policy goes on, counted by running the policy's rule.
  function scheduled(ex: Exec, api: string, v: V, policy: ts.Expression, at: ts.CallExpression): V {
    const use = api === 'Effect.retry' ? 'retry' : 'repeat', pol = strip(policy)
    if (v.t !== 'eff') return refuse(at, `${api} of other than an effect`)
    let sched: ts.Expression | undefined, times: number | undefined
    if (ts.isObjectLiteralExpression(pol)) {
      for (const pr of pol.properties) {
        const k = ts.isPropertyAssignment(pr) ? memberName(pr.name) : ''
        if (k === 'schedule') sched = (pr as ts.PropertyAssignment).initializer
        else if (k === 'times') { const n = strip((pr as ts.PropertyAssignment).initializer); times = ts.isNumericLiteral(n) ? Number(n.text) : refuse(n, `${use}'s times of other than a number written here`) }
        else if ((k === 'while' || k === 'until') && use === 'retry') s.notes.add(`${use}'s ${k} reads the error: each attempt fails with the same one, so it decides only how many attempts are made`)
        else return refuse(pr, `${use}'s ${text(pr)} (schedule, times${use === 'retry' ? ', while and until' : ''} are read)`)
      }
    } else sched = pol
    const outer = (n: ts.Node): never => refuse(n, `${text(n)}: a ${use} policy reading the service's params (one written with literals and consts is read: the check runs it)`)
    const P = new Parts(), base = sched ? readSchedule(sched, {api: x => apiOf(s, x), checker: s.checker, v4: V4, params: new Map(), sf: s.sf, outer}, P) : undefined
    let frag = base?.frag
    if (times !== undefined) { const lim = (frag ?? {step: () => ({cont: dsl.yes, delay: dsl.lit(0), next: {}}), names: []}) as typeof frag & object, n = times; frag = {...lim, step: (env, get, c) => { const x = lim.step(env, get, c); return {...x, cont: x.cont.and(c.attempt.lt(n))} }} }
    if (!frag) return refuse(at, `${use} with no schedule and no times (it would go on forever)`)
    const sr = scheduleRule(frag, P, `${use} policy`, V4)
    // (a method may be read more than once: one entry a place)
    if (!found.some(f => f.at === where(at))) found.push({at: where(at), use, source: sched ? sched.getText() : `{times: ${times}}`, rule: sr})
    // The policy run as Effect drives it, each attempt taking no time: how many times it goes on (for every input it
    // may be fed, drawn), and how long it waits in all.
    const g = sr.rule.compiled(), ps = sr.rule.encodeParams({} as never), rand = (() => { let x = 7; return (n: number) => (x = (x * 1103515245 + 12345) % 2147483648) % Math.max(1, n) })()
    const runOnce = (draw: boolean) => {
      let st = g.init(ps), n = 0, waited = 0
      for (; n < 1000; n++) {
        const inp: Record<string, unknown> = {took: 0}
        for (const [f, k] of sr.fields) inp[f === '_tag' ? 'input__tag' : f === 'input' ? 'input' : `input_${f}`] = (k as never as {sample: (r: (n: number) => number, b: number) => unknown}).sample(draw ? rand : () => 0, 3)
        for (const j of sr.jitters) inp[j.name] = 0
        try { st = g.step(ps, st, sr.rule.encodeInput(inp as never)) } catch { return {stops: true, n, waited} }
        const d = sr.rule.decode(st) as Record<string, number | boolean>
        if (d.done) return {stops: true, n, waited}
        waited += Number(d.delay)
      }
      return {stops: false, n, waited}
    }
    const runs = [runOnce(false), ...(sr.fields.size ? Array.from({length: 8}, () => runOnce(true)) : [])]
    if (runs.some(r => !r.stops)) return refuse(policy, `a ${use} whose policy goes on past 1000 attempts${use === 'retry' ? ' around an effect read here, which fails the same way each time: the call would never return' : ''} (bound it: recurs, upTo, times)`)
    if (sr.jitters.length) s.notes.add(`the ${use} policy's jitter is left to its rule (x.schedules): it moves only the time the step waits`)
    if (use === 'retry') {
      s.notes.add(`${text(at)}: retried with ${sched ? text(sched) : `{times: ${times}}`}; each attempt fails as the first did (the effect reads only the Refs, which a failure leaves as they were), so the step is the effect's; the policy's own laws are proven on its rule (x.schedules)`)
      return eff(q => withoutClock(ex, 'the clock read in an effect that is retried (each attempt reads a later time: a loop the step doesn\'t unroll)', () => v.run(q)))
    }
    if (sr.fields.size) return refuse(sched!, 'a repeat whose policy reads the effect\'s result (a loop the step doesn\'t unroll)')
    const n = runs[0]!.n, waited = runs[0]!.waited
    if (n > 16) return refuse(policy, `a repeat that runs the effect ${n + 1} times (up to 17 are unrolled)`)
    let host: ts.Node = at
    while (host.parent && (ts.isCallExpression(host.parent) || ts.isParenthesizedExpression(host.parent) || ts.isPropertyAccessExpression(host.parent))) host = host.parent
    if (!ts.isYieldExpression(host.parent) || !ts.isExpressionStatement(host.parent.parent)) return refuse(at, 'the value of a repeat (its policy\'s output): yield* it as a statement')
    s.notes.add(`${text(at)}: the effect runs ${n + 1} times in the step (its policy goes on ${n} times)${waited ? `, waiting ${waited} ms in all` : ''}`)
    return eff(q => {
      let r: [V, Path] = [undef, q]
      withoutClock(ex, 'the clock read in an effect that is repeated (each run reads a later time)', () => { for (let i = 0; i <= n; i++) r = v.run(r[1]) })
      return [undef, waited ? {...r[1], heap: new Map(r[1].heap).set(SLEPT, flagged(I.T))} : r[1]]
    })
  }
  // f run with the clock refused where it is read (an effect run again later in the step reads a later time).
  function withoutClock<T>(ex: Exec, why: string, f: () => T): T {
    const own = Object.getOwnPropertyDescriptor(ex, 'now')
    Object.defineProperty(ex, 'now', {value: (n: ts.Node) => refuse(n, why), configurable: true, writable: true})
    try { return f() } finally { if (own) Object.defineProperty(ex, 'now', own); else delete (ex as {now?: unknown}).now }
  }
  // Ref.op(ref, ...): the ref a Ref the service made (by its name), its value the state's field.
  function refOp(ex: Exec, e: ts.CallExpression, m: string, op: string, p: Path): [V, Path] {
    const r = e.arguments[0] && strip(e.arguments[0]), base = op.replace(/Effect$/, ''), answer = ANSWERS[base], f = e.arguments[1]
    if (MAKES.includes(op)) return refuse(e, `${m}.${op} in a step (each call would make a new Ref: the service's Refs are made by its make effect)`)
    if (!r) return refuse(e, `${m}.${op} with no Ref`)
    if (!answer) return refuse(e, `${m}.${op} (get, set, update, modify, updateAndGet, getAndUpdate, getAndSet and setAndGet are read)`)
    const name = ts.isIdentifier(r) && refs.has(r.text) && s.closure?.has(s.checker.getSymbolAtLocation(r)?.valueDeclaration as ts.Node) ? r.text : refuse(r, `${text(r)}: a Ref other than one the service's make effect makes (a Ref held in a value, or given to it)`)
    const self: V = {t: 'ref', id: 'this'}
    // A Ref set to a value: where it is the one it held, nothing changes.
    const put = (v: V, q: Path): Path => {
      const changed = changedOf(v, ex.field(self, name, r, q)[0])
      if (changed.op === 'const' && !changed.v) return q
      const [w, q2] = ex.whole(v, q, r), q3 = ex.writeField(self, name, w, q2, r)
      return {...q3, heap: new Map(q3.heap).set(CHANGED, {k: 'alias', to: {t: 'bool', e: I.or(changedOn(q3), changed)}})}
    }
    // The new value: the one given (set), or the function's of the old (update, modify: a function written here).
    const locals = p.locals, fn = base === 'get' || /[sS]et/.test(base) ? undefined : f && (fnOf(s, f) ?? (ts.isIdentifier(f) ? (d => (d && ts.isFunctionDeclaration(d) && s.ours(d.getSourceFile()) ? d : undefined))(s.checker.getSymbolAtLocation(f)?.valueDeclaration) : undefined))
    if (base !== 'get' && !/[sS]et/.test(base) && (!fn || fn.asteriskToken)) return f ? refuse(f, `${m}.${op} of other than a function written here`) : refuse(e, `${m}.${op} with no function`)
    const [given, q0] = /[sS]et/.test(base) ? ex.ev(f ?? refuse(e, `${m}.${op} with no value`), p) : [undefined, p]
    return [eff(q => {
      const [c, q1] = ex.field(self, name, r, q)
      if (base === 'get') return [c, q1]
      let [v, q2]: [V, Path] = given ? [given, q1] : ex.inline({decl: fn!}, [c], f!, q1, ts.isIdentifier(f!) ? new Map() : locals)
      if (/Effect$/.test(op)) [v, q2] = v.t === 'eff' ? v.run(q2) : refuse(f!, `${m}.${op}'s function returns other than an effect`)
      if (base === 'modify') {
        if (v.t !== 'tuple' || v.xs.length !== 2) return refuse(f!, `${m}.${op}'s function returns other than [result, value]`)
        return [v.xs[0]!, put(v.xs[1]!, q2)]
      }
      return [answer === 'old' ? c : answer === 'new' ? v : undef, put(v, q2)]
    }), q0]
  }
}

// --- running the code -----------------------------------------------------------------------------------------------
// Effects run synchronously on the Effect given (3.x or 4.x), the clock fixed at the request's time; a failure (a typed
// one, a defect, or an effect that would wait) is thrown, as the check reads a refusal.
export type Runner = {run: (eff: unknown, now?: number) => unknown, exit: (eff: unknown, now: number) => {ok: true, value: unknown} | {ok: false, error: string}, get: (mod: string, ref: unknown) => unknown, set: (mod: string, ref: unknown, v: unknown) => unknown}
export function runner(E: Mod): Runner {
  const {Effect, Exit, Cause, Clock} = E, v4 = 'TxRef' in E
  if (!Effect?.runSyncExit) throw new Error('effect: give the `effect` package itself (import * as effect from \'effect\')')
  let now = 0
  // A Clock at `now`: 4.x names its unsafe reads currentTime<X>Unsafe, 3.x unsafeCurrentTime<X>.
  const unsafe = (x: string) => (v4 ? `currentTime${x}Unsafe` : `unsafeCurrentTime${x}`), ns = () => BigInt(now) * 1_000_000n
  // (a sleep, a retry's or a repeat's, passes at once: the clock moves on by its duration)
  const clock = Object.create(Effect.runSync(v4 ? Effect.clockWith((c: unknown) => Effect.succeed(c)) : Effect.clock), {[unsafe('Millis')]: {value: () => now}, currentTimeMillis: {value: Effect.sync(() => now)}, [unsafe('Nanos')]: {value: ns}, currentTimeNanos: {value: Effect.sync(ns)},
    sleep: {value: (d: unknown) => Effect.sync(() => { now += E.Duration.toMillis(d) })}})
  const exit = (eff: unknown, t: number): {ok: true, value: unknown} | {ok: false, error: string} => {
    if (!Effect.isEffect(eff)) return {ok: false, error: `not an effect: ${String(eff).slice(0, 60)}`}
    now = t
    // (3.x on a scheduler of its own, so a fiber left waiting, a transaction that retries, is interrupted at once: it
    // would otherwise wake and commit inside a later request)
    let x: Mod, waiting: {fiber: Mod} | undefined
    if (v4) {
      x = Effect.runSyncExit(Effect.provideService(eff, Clock.Clock, clock))
      waiting = Exit.isSuccess(x) ? undefined : (x.cause.reasons ?? []).map((r: {defect?: unknown}) => r.defect).find((d: unknown) => d && typeof d === 'object' && 'fiber' in d)
      waiting?.fiber.interruptUnsafe()
    } else {
      // (on a scheduler of its own: what yields to it (a SynchronizedRef's lock) runs on when it is flushed; a fiber still
      // waiting then is interrupted there)
      const sch = new E.Scheduler.SyncScheduler()
      x = Effect.runSyncExit(Effect.withScheduler(Effect.withClock(eff, clock), sch))
      const fiber = Exit.isSuccess(x) ? undefined : (x.cause.defect as {fiber?: Mod} | undefined)?.fiber
      if (fiber) {
        for (let i = 0; i < 64 && !(x = fiber.unsafePoll()); i++) sch.flush()
        if (!x) { waiting = {fiber}; fiber.unsafeInterruptAsFork(E.FiberId.none); sch.flush() }
      }
    }
    if (x && Exit.isSuccess(x)) return {ok: true, value: x.value}
    return {ok: false, error: waiting ? 'it waits (an effect that suspends: a transaction that retries, a fiber it waits for)' : String(Cause.pretty(x.cause)).split('\n')[0]!}
  }
  const run = (eff: unknown, t = now) => { const x = exit(eff, t); if (!x.ok) throw new Error(x.error); return x.value }
  return {run, exit, get: (mod, ref) => run(E[mod].get(ref)), set: (mod, ref, v) => run(E[mod].set(ref, v))}
}

export function extractEffect(at: Source, opts: EffectOptions = {}): Extraction {
  let m, code: string, file: string, E: Mod | undefined
  try {
    ;({code, file} = sourceOf(at, opts.file, 'input.ts'))
    E = opts.effect ?? beside<Mod>(file, 'effect')
    if (!E) throw new Refusal(file, 'no effect package resolves from the file (install it in its project, or give it: {effect: await import(\'effect\')})')
    V4 = 'TxRef' in E; found = []
    const sch = scheduleEntry(code, file, opts)
    if (sch) return fromScheduleEntry(code, file, sch, E, opts)
    const entry = opts.entry ?? serviceOf(code, file, opts)
    if (opts.fibers !== false) { const f = fibered(code, file, entry, E, opts); if (f) return f }
    m = readFactory(code, placed(file), {...opts, entry}, s => factoryOf(s, entry)); m.file = file
    if (!opts.entry) m.notes.unshift(`the entry inferred: ${entry}, the file's one make effect`)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  // The modules the code imports, by specifier (effect, effect/<Module>), and the check's runner.
  const model = m, modules = {effect: E, ...Object.fromEntries(Object.entries(E).map(([k, x]) => [`effect/${k}`, x])), 'gdp-wired:effect': runner(E), ...opts.modules}
  const schedules = found
  return {...fromModel(model, file, opts.domains, [], (rule, sorts) => check(code, file, model, rule, sorts, {...opts.check, modules, ...(opts.files ? {files: opts.files} : {}), ...(opts.domains ? {given: opts.domains} : {})})), names: namesOf(model), ...(schedules.length ? {schedules} : {})} as Extraction
}
// --- many fibers: a method that is several steps ---------------------------------------------------------------------
// A method's atomic units: the statements of its body that run an effect on the service's state (a transaction, a Ref
// operation, a helper's), each a step another fiber's may come between. A failure, a log, a sleep or a wait runs no
// such effect. A method of two or more is read as its steps: the service written again with one fiber's place in it
// (`__pc`) and what it carries from one step to the next (its arguments, its locals) in Refs of its own, read and
// checked as any service; then lift (core/system.ts) makes those Refs every fiber's at once (maps keyed by `fiber`, an
// input), the service's own Refs shared, and each request one fiber's next step.
const QUIET = new Set(['Effect.fail', 'Effect.failSync', 'Effect.die', 'Effect.dieMessage', 'Effect.void', 'Effect.sleep', 'Effect.yieldNow', 'Effect.txRetry', 'STM.fail', 'STM.die', 'STM.retry', ...[...LOGS].map(l => `Effect.${l}`)])
const TX = /\b(TRef|TxRef|STM)\.|Effect\.tx\b/
function fibered(code: string, file: string, entry: string, E: Mod, opts: EffectOptions): Extraction | undefined {
  const s = setupOf(code, placed(file), {}, opts.files), f = factoryOf(s, entry)
  const yields = (n: ts.Node): ts.YieldExpression[] => { const out: ts.YieldExpression[] = []; const go = (x: ts.Node) => { if (ts.isYieldExpression(x)) out.push(x); if (!ts.isFunctionLike(x)) ts.forEachChild(x, go) }; ts.forEachChild(n, go); if (ts.isYieldExpression(n)) out.unshift(n); return out }
  const quiet = (y: ts.YieldExpression) => { const x = y.expression && strip(y.expression); return !x || ts.isNewExpression(x) || QUIET.has((ts.isCallExpression(x) ? callOf(s, x) : apiOf(s, x)) ?? '') }
  const failing = (y: ts.YieldExpression) => { const x = y.expression && strip(y.expression); return !!x && (ts.isNewExpression(x) || /^(Effect|STM)\.(fail|failSync|die|dieMessage)$/.test((ts.isCallExpression(x) ? callOf(s, x) : '') ?? '')) }
  // The methods: each property of the returned object, its function where the make effect writes it.
  type M = {name: string, fn: ts.FunctionExpression, at: ts.Expression, units: number[], stmts: readonly ts.Statement[]}
  const methods: M[] = []
  for (const pr of f.obj.properties) {
    const name = pr.name ? memberName(pr.name) : ''
    let init: ts.Expression | undefined = ts.isPropertyAssignment(pr) ? pr.initializer : ts.isShorthandPropertyAssignment(pr) ? pr.name : undefined
    if (init && ts.isIdentifier(strip(init))) { const d = (ts.isShorthandPropertyAssignment(pr) ? s.checker.getShorthandAssignmentValueSymbol(pr) : s.checker.getSymbolAtLocation(strip(init)))?.valueDeclaration; init = d && ts.isVariableDeclaration(d) ? d.initializer : init }
    const fn = init && fnOf(s, init)
    if (!fn || !ts.isFunctionExpression(fn) || !fn.asteriskToken || !fn.body) continue
    const stmts = fn.body.statements, units = stmts.flatMap((st, i) => (yields(st).some(y => !quiet(y)) ? [i] : []))
    methods.push({name, fn, at: init!, units, stmts})
  }
  const split = methods.filter(mt => mt.units.length >= 2)
  if (!split.length || (opts.fibers === undefined && !TX.test(code))) {
    if (split.length) s.notes.add(`${split.map(mt => mt.name).join(', ')} run several Ref operations one after another: each method is read as one step, which holds where calls don't interleave (fibers: true reads them as interleaving steps)`)
    return undefined
  }
  // Each split method's segments, the names each carries on, and the service written again.
  const edits: [number, number, string][] = [], decls: string[] = [], resumes: string[] = []
  const tyOf = (n: ts.Node) => { const t = s.checker.getTypeAtLocation(n), str = s.checker.typeToString(s.checker.getBaseTypeOfLiteralType(t)); return t.flags & ts.TypeFlags.BooleanLike ? ['boolean', 'false'] : t.flags & ts.TypeFlags.NumberLike ? ['number', '0'] : t.isUnion() && t.types.every(u => u.isStringLiteral()) ? [s.checker.typeToString(t), JSON.stringify((t.types[0] as ts.StringLiteralType).value)] : t.flags & ts.TypeFlags.StringLike ? ['string', "''"] : refuse(n, `${text(n)} is carried from one step to the next, and is a ${str} (a number, a boolean or a string is carried)`) }
  split.forEach((mt, mi) => {
    const base = (mi + 1) * 100, K = mt.units.length, segs: ts.Statement[][] = []
    mt.units.forEach((u, k) => segs.push([...mt.stmts.slice(k === 0 ? 0 : mt.units[k - 1]! + 1, u + 1), ...(k === K - 1 ? mt.stmts.slice(u + 1) : [])]))
    for (const [k, seg] of segs.entries()) for (const st of seg) {
      const ys = yields(st).filter(y => !quiet(y))
      if (ys.length > 1) refuse(st, `${mt.name}: ${text(st)} runs ${ys.length} effects on the state in one statement (write each in a statement of its own: each is a step)`)
      // (a later step's failing transaction: the call would end with the earlier steps' writes kept and this one's rolled
      // back, which a refusal of this step leaves the fiber waiting on instead)
      if (k > 0) { const go = (x: ts.Node, inner: boolean) => { if (ts.isYieldExpression(x) && inner && failing(x)) refuse(x, `${mt.name}: a transaction that fails in a step after the first (the call ends there, its earlier steps' writes kept): fail in the first step, or wait (STM.check, Effect.txRetry) instead`); ts.forEachChild(x, c => go(c, inner || ts.isFunctionLike(x))) }; go(st, false) }
    }
    // What a later step reads of an earlier one: the arguments and the locals declared at the top of a segment.
    const carried = new Map<ts.Node, string>()
    for (const p of mt.fn.parameters) if (ts.isIdentifier(p.name)) carried.set(p, p.name.text)
    segs.forEach(seg => seg.forEach(st => { if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) carried.set(d, ts.isIdentifier(d.name) ? d.name.text : refuse(d, `${mt.name}: ${text(d)} (a name is carried, not a pattern)`)) }))
    const usedIn = (seg: ts.Statement[]) => { const u = new Set<ts.Node>(); const go = (x: ts.Node) => { if (ts.isIdentifier(x)) { const d = s.checker.getSymbolAtLocation(x)?.valueDeclaration; if (d && carried.has(d)) u.add(d) } ts.forEachChild(x, go) }; seg.forEach(go); return u }
    const later = segs.map((_, k) => { const u = new Set<ts.Node>(); segs.slice(k + 1).forEach(sg => usedIn(sg).forEach(d => u.add(d))); return u })
    const ref = (d: ts.Node) => `__${mt.name}_${carried.get(d)}`
    const kept = new Set<ts.Node>(); later.forEach(u => u.forEach(d => kept.add(d)))
    for (const d of kept) { const [t, zero] = tyOf(d); decls.push(`const ${ref(d)} = yield* __Ref.make<${t}>(${zero})`) }
    // (where each carried name is defined: a parameter, or the segment that declares it)
    const defined = (d: ts.Node, k: number) => (ts.isParameter(d) ? k === 0 : segs[k]!.some(st => st.pos <= d.pos && d.end <= st.end))
    const body = (seg: ts.Statement[], k: number) => {
      const loads = k === 0 ? '' : [...usedIn(seg)].filter(d => !defined(d, k)).map(d => `const ${carried.get(d)} = yield* __Ref.get(${ref(d)})\n`).join('')
      const stores = [...later[k]!].filter(d => defined(d, k) || ts.isParameter(d) && k === 0).map(d => `yield* __Ref.set(${ref(d)}, ${carried.get(d)})\n`).join('')
      // (in a later step, a return ends the call: the fiber goes back to where it starts; a failure outside a transaction
      // too, as a return (the earlier steps' writes kept, as Effect keeps them); a wait leaves it where it is)
      const textOf = (st: ts.Statement): string => {
        if (k === 0) return st.getText()
        let t = st.getText(); const rs: ts.Node[] = []
        const go = (x: ts.Node) => { if (ts.isReturnStatement(x) || ts.isExpressionStatement(x) && ts.isYieldExpression(strip(x.expression)) && failing(strip(x.expression) as ts.YieldExpression)) rs.push(x); if (!ts.isFunctionLike(x)) ts.forEachChild(x, go) }
        go(st)
        for (const r of rs.reverse()) {
          const y = ts.isReturnStatement(r) ? r.expression && strip(r.expression) : strip((r as ts.ExpressionStatement).expression), fails = !!y && ts.isYieldExpression(y) && failing(y)
          if (y && ts.isYieldExpression(y) && quiet(y) && !fails) continue
          t = t.slice(0, r.getStart() - st.getStart()) + `{ yield* __Ref.set(__pc, 0); ${fails ? 'return' : r.getText()} }` + t.slice(r.end - st.getStart())
        }
        return t
      }
      return `${loads}${seg.map(textOf).join('\n')}\n${stores}yield* __Ref.set(__pc, ${k === K - 1 ? 0 : base + k + 2})`
    }
    resumes.push(...segs.slice(1).map((seg, j) => `if (__p === ${base + j + 2}) {\n${body(seg, j + 1)}\n}`))
    const params = mt.fn.parameters.map(p => p.getText()).join(', ')
    edits.push([mt.fn.getStart(), mt.fn.end, `function* (${params}) {\nconst __p = yield* __Ref.get(__pc)\nif (__p !== 0) return yield* __resume()\n${body(segs[0]!, 0)}\n}`])
  })
  const ret = (f.fn.body as ts.Block).statements.at(-1)!
  edits.push([ret.getStart(), ret.getStart(), `const __pc = yield* __Ref.make<number>(0)\n${decls.join('\n')}\nconst __resume = __Effect.fn('__resume')(function* () {\nconst __p = yield* __Ref.get(__pc)\n${resumes.join(' else ')}\n})\n`])
  let out = code
  for (const [a, b, t] of edits.sort((x, y) => y[0] - x[0])) out = out.slice(0, a) + t + out.slice(b)
  out = `import {Effect as __Effect, Ref as __Ref} from 'effect'\n${out}`
  // One fiber: the service written again, read and checked as any.
  const one = extractEffect(out, {...opts, file, entry, effect: E, fibers: false})
  if (!one.ok || !one.rule) return {...one, notes: [`read as one fiber's steps (${split.map(mt => `${mt.name}: ${mt.units.length}`).join(', ')}), the service written again:`, out, ...one.notes]}
  const m0 = one.rule.machine, model = one.model!
  const local = (n: string) => n.startsWith('__') || model.outputs.some(o => n === o || n.startsWith(`${o}_`)) || n === 'failed'
  const shared = Object.keys(m0.state).filter(n => !local(n))
  if (m0.inputs.includes('fiber')) return {ok: false, refusals: [{where: file, what: 'a method takes an argument named fiber (the name the fibers are told apart by)'}], notes: []}
  const lifted = lift(m0, 'fiber', shared)
  const parts = (one.rule as never as {parts: {params: [string, dsl.Kind<unknown>][], inputs: [string, dsl.Kind<unknown>][]}}).parts
  // (the kinds of the requests' choices kept; an integer is its two naturals, x and x$neg, as the machine has it)
  const named = new Set([...lifted.params, ...lifted.inputs]), whole = ([n]: [string, unknown]) => named.has(n) && !named.has(`${n}$neg`)
  const rule = asRule({...lifted, name: `${m0.name}, every fiber`}, Object.fromEntries([...parts.params, ...parts.inputs].filter(whole)))
  const names = (one.names ?? []).filter(n => !(n.role === 'state' && local(n.rule)) && n.role !== 'result' && !n.code.startsWith('__'))
  const inv = (one.invariants ?? []).filter(l => !JSON.stringify(l.holds).match(/"name":"(__[^"]*|[^"]*_result[^"]*)"/))
  const steps = split.map((mt, mi) => ({name: mt.name, steps: mt.units.length, base: (mi + 1) * 100}))
  return {...one, rule, names: [...names, {code: 'fiber', rule: 'fiber', role: 'input'}], invariants: inv, fibers: steps, replay: undefined,
    notes: [`calls from many fibers at once: ${split.map(mt => `${mt.name} is ${mt.units.length} steps`).join(', ')} (each transaction or Ref operation one), the fibers interleaving them: the rule is every fiber's (lift: each fiber's place and what it carries a map keyed by the input fiber, the service's Refs (${shared.join(', ')}) shared); each other method is one step. A request is one fiber's next step: a fiber in the middle of a call takes its next step whatever method the request names. A failure in a later step ends the call as a return does. A law reads the service's Refs`, ...one.notes],
    source: out}
}

// A run of every fiber's rule as what each fiber does: starts a call (with its arguments), or takes the next step of the
// call it is in.
export function fiberRun(x: Extraction, run: {params: Record<string, number>, trace: Record<string, unknown>[]}): string[] {
  const fibers = (x as {fibers?: {name: string, steps: number, base: number}[]}).fibers ?? [], r = x.rule as never as {machine: dsl.Rule['machine'], parts: {inputs: [string, dsl.Kind<unknown>][]}, encodeParams: (p: unknown) => Record<string, number>}
  const go = interpret(r.machine), ps = r.encodeParams(run.params), method = new Map(r.parts.inputs).get('method') as {decode: (n: string, v: unknown) => string} | undefined
  let st = go.init(ps)
  return run.trace.map(q => {
    const f = Number(q.fiber), pc = st.maps.__pc?.get(f) ?? 0, m = method ? method.decode('method', q) : x.model?.events[0]?.call ?? 'step'
    st = go.step(ps, st, q as never)
    if (pc === 0) {
      const sp = fibers.find(s2 => s2.name === m), args = (x.names ?? []).filter(n => n.role === 'input' && n.method === m && n.rule in q).map(n => `${n.code.split('.').pop()} = ${String(q[n.rule])}`)
      return `fiber ${f}: ${m}(${args.join(', ')})${sp ? `, its step 1 of ${sp.steps}` : ''}`
    }
    const sp = fibers.find(s2 => pc > s2.base && pc <= s2.base + s2.steps)!
    return `fiber ${f}: ${sp.name}, its step ${pc - sp.base} of ${sp.steps}`
  })
}

// --- a schedule as the entry ------------------------------------------------------------------------------------------
// A declaration whose value is a Schedule (or a function returning one, its parameters the rule's params): the named
// entry, else the file's one schedule where it has no service.
type SchedEntry = {name: string, expr: ts.Expression, params: string[], s: Setup}
const isSchedule = (s: Setup, e: ts.Expression): boolean => {
  e = strip(e)
  if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && memberName(e.expression.name) === 'pipe' && !apiOf(s, e.expression)) return isSchedule(s, e.expression.expression)
  return (ts.isCallExpression(e) ? apiOf(s, e.expression) : apiOf(s, e))?.startsWith('Schedule.') ?? false
}
function scheduleEntry(code: string, file: string, opts: EffectOptions): SchedEntry | undefined {
  if (!/\bSchedule\b/.test(code)) return undefined
  const s = setupOf(code, placed(file), {}, opts.files), found: SchedEntry[] = []
  for (const st of s.sf.statements) {
    const decls = ts.isVariableStatement(st) ? st.declarationList.declarations.filter(d => ts.isIdentifier(d.name) && d.initializer).map(d => [(d.name as ts.Identifier).text, d.initializer!] as const)
      : ts.isFunctionDeclaration(st) && st.name ? [[st.name.text, st] as const] : []
    for (const [name, init] of decls) {
      if (opts.entry && opts.entry !== name) continue
      const f = ts.isFunctionDeclaration(init) ? init : ts.isArrowFunction(strip(init as ts.Expression)) || ts.isFunctionExpression(strip(init as ts.Expression)) ? strip(init as ts.Expression) as ts.FunctionLikeDeclaration : undefined
      const body = f ? lastReturn(f.body) : init as ts.Expression
      if (!body || !isSchedule(s, body) || (f && ts.isBlock(f.body!) && f.body.statements.length > 1)) continue
      found.push({name, expr: body, params: (f?.parameters ?? []).map(p => (ts.isIdentifier(p.name) ? p.name.text : refuse(p, `${text(p)}: a parameter other than a name`))), s})
    }
  }
  if (opts.entry) return found[0]
  // (a file with a service reads the service; else its one schedule, the exported ones first)
  if (found.length === 0) return undefined
  try { serviceOf(code, file, opts); return undefined } catch (e) { if (!(e instanceof Refusal)) throw e }
  const exported = found.filter(f => new RegExp(`export\\s+(?:const|function)\\s+${f.name}\\b`).test(code))
  const pick = exported.length ? exported : found
  if (pick.length > 1) throw new Refusal(file, `several schedules in the file (${pick.map(f => f.name).join(', ')}): name one (entry)`)
  return pick[0]
}
// The schedule read into its rule, and checked by stepping the file's own schedule on Effect beside it.
function fromScheduleEntry(code: string, file: string, e: SchedEntry, E: Mod, opts: EffectOptions): Extraction {
  const t0 = Date.now(), v4 = 'TxRef' in E, s = e.s
  const params = new Map<ts.Node, string>()
  const fnDecl = (() => { let n: ts.Node | undefined = e.expr; while (n && !ts.isFunctionLike(n)) n = n.parent; return n as ts.FunctionLikeDeclaration | undefined })()
  for (const p of fnDecl?.parameters ?? []) if (ts.isIdentifier(p.name)) params.set(p, p.name.text)
  const P = new Parts()
  for (const n of e.params) P.params.set(n, dsl.nat)
  let sr: ScheduleRule
  try { sr = scheduleRule(readSchedule(e.expr, {api: x => apiOf(s, x), checker: s.checker, v4, params, sf: s.sf}, P).frag, P, e.name, v4) } catch (x) {
    if (x instanceof Refusal) return {ok: false, refusals: [{where: x.where, what: x.what}], notes: []}
    throw x
  }
  const notes = [`${e.name} is an Effect ${v4 ? '4' : '3'} Schedule: each step is one of its decisions (go on after a delay, or stop), at the time the attempt before it ended; attempt, retries, delay, elapsed and done are the rule's own${e.params.length ? `; its parameters (${e.params.join(', ')}) are the rule's params, naturals` : ''}`, ...sr.notes]
  const modules = {effect: E, ...Object.fromEntries(Object.entries(E).map(([k, x]) => [`effect/${k}`, x])), ...opts.modules}
  const box = sandbox(code, file, [e.name], modules, undefined, opts.files)
  const value = box.get(e.name), make = (p: Record<string, number>) => (typeof value === 'function' ? (value as (...a: number[]) => unknown)(...e.params.map(n => p[n]!)) : value)
  const runs = (opts.check as {runs?: number} | undefined)?.runs ?? 60, c = scheduleConforms(sr, make, E, {runs, depth: 14})
  const evidence = {runs, requests: c.checked, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: c.checked, coverage: {arms: 0, hit: 0, missed: []}, ms: Date.now() - t0, ...(c.failure ? {mismatch: c.failure} : {})}
  const source = `// ${e.name}: ${e.expr.getText().replace(/\s+/g, ' ')}\n${sr.rule.machine.name}: state ${Object.keys(sr.rule.machine.state).join(', ')}; inputs ${sr.rule.machine.inputs.join(', ')}${sr.rule.machine.params.length ? `; params ${sr.rule.machine.params.join(', ')}` : ''}`
  if (c.failure) return {ok: false, rule: sr.rule, source, refusals: [{where: file, what: `the rule and Effect's own schedule part: ${c.failure}`}], notes, names: sr.names, evidence}
  return {ok: true, rule: sr.rule, source, refusals: [], notes, names: sr.names, evidence, schedule: sr, replay: run => replaySchedule(sr, make(run.params), E, run)} as Extraction
}
// A schedule written as source (an expression over Schedule and Duration, with `params` its free names) read into its
// rule and checked against the schedule Effect makes of it: fromSchedule('Schedule.exponential("10 millis").pipe(Schedule.upTo({times: 5}))', {effect}).
export function fromSchedule(source: string, opts: {effect: Mod, params?: string[], name?: string, runs?: number}): Extraction {
  const ps = opts.params ?? [], name = opts.name ?? 'schedule'
  const code = `import {Duration, Effect, Schedule} from 'effect'\nexport const ${name} = (${ps.map(p => `${p}: number`).join(', ')}) => ${source}\n`
  return extractEffect(code, {file: 'schedule.ts', entry: name, effect: opts.effect, check: {runs: opts.runs ?? 60}} as EffectOptions)
}

// The service a file has: of its declarations (the exported ones first), those whose make effect reads, one make effect
// however many names reach it (make, and a Layer of it).
function serviceOf(code: string, file: string, opts: EffectOptions): string {
  const s = setupOf(code, placed(file), {}, opts.files), found: [string, ts.Node][] = []
  const exported = (st: ts.Statement) => !!(ts.canHaveModifiers(st) && ts.getModifiers(st)?.some(x => x.kind === ts.SyntaxKind.ExportKeyword))
  for (const pass of [true, false]) {
    for (const st of s.sf.statements.filter(x => exported(x) === pass)) {
      const names = ts.isVariableStatement(st) ? st.declarationList.declarations.flatMap(d => (ts.isIdentifier(d.name) ? [d.name.text] : []))
        : (ts.isFunctionDeclaration(st) || ts.isClassDeclaration(st)) && st.name ? [st.name.text, ...(ts.isClassDeclaration(st) ? st.members.flatMap(x => (ts.isPropertyDeclaration(x) && ts.isIdentifier(x.name) ? [`${st.name!.text}.${x.name.text}`] : [])) : [])] : []
      for (const n of names) { try { const f = factoryOf(s, n); if (!found.some(([, g]) => g === f.fn)) found.push([n, f.fn]) } catch (e) { if (!(e instanceof Refusal)) throw e } }
    }
    if (found.length) break
  }
  if (found.length > 1) throw new Refusal(file, `several services in the file (${found.map(([n]) => n).join(', ')}): name one (entry)`)
  return found[0]?.[0] ?? refuse(s.sf.statements[0] ?? s.sf, 'no make effect in the file (an Effect.gen whose Refs its methods write, a function returning one, Effect.fn, or Layer.effect of one): name the entry')
}

// A rule written by hand beside a running service: `runs` runs of `depth` requests drawn by `draw` (the rule's inputs),
// each made of the service by `request` (an effect, run with the clock at the input named by `now`) and of the rule.
// They must fail together (the rule's assumption or step refuses where the effect fails), and after each step every
// field `observe` reads of the service (an effect or a value) must be the rule's state's, or `view`'s of it.
export type Service<S> = {
  effect: Mod,
  make: (params: Record<string, unknown>) => unknown,
  request: (service: S, input: Record<string, unknown>, params: Record<string, unknown>) => unknown,
  // eslint-disable-next-line @typescript-eslint/no-explicit-any
  observe?: (service: S, result: any, input: Record<string, unknown>) => unknown,
  view?: (state: Record<string, unknown>, input: Record<string, unknown>) => Record<string, unknown>,
  now?: string,
}
export function conforms<S>(r: Rule, svc: Service<S>, opts: {draw: (rand: Rand) => Record<string, unknown>, params?: (rand: Rand) => Record<string, unknown>, runs?: number, depth?: number, seed?: number}): {checked: number, failure?: string} {
  const R = runner(svc.effect), rand = seeded(opts.seed ?? 1), g = r.compiled(), interp = interpret(r.machine), isEffect = (x: unknown) => svc.effect.Effect.isEffect(x) as boolean
  let checked = 0
  for (let run = 0; run < (opts.runs ?? 100); run++) {
    const params = opts.params?.(rand) ?? {}, ps = r.encodeParams(params as never), m0 = svc.make(params), made = isEffect(m0) ? R.exit(m0, 0) : {ok: true as const, value: m0}
    if (!made.ok) return {checked, failure: `the service with ${JSON.stringify(params)} fails to be made: ${made.error}`}
    const self = made.value as S, sent: string[] = []
    let st = g.init(ps)
    for (let d = 0; d < (opts.depth ?? 12); d++) {
      const input = opts.draw(rand), now = svc.now ? Number(input[svc.now]) : 0
      let enc, ok: boolean
      try { enc = r.encodeInput(input as never, params as never) } catch (e) { return {checked, failure: `${JSON.stringify(input)} is outside the rule's inputs: ${(e as Error).message}`} }
      sent.push(JSON.stringify(input))
      const at = `${Object.keys(params).length ? `with ${JSON.stringify(params)}, ` : ''}after ${sent.join(', ')}`
      try { ok = allowed(r.machine, interp, ps, st, enc) && (g.step(ps, g.fork(st), enc), true) } catch { ok = false }
      const x = R.exit(svc.request(self, input, params), now)
      if (ok !== x.ok) return {checked, failure: `${at}: the ${x.ok ? 'service takes the request' : `service fails (${(x as {error: string}).error})`}, the rule ${ok ? 'takes it' : 'refuses it'}`}
      if (!ok) continue
      st = g.step(ps, st, enc)
      if (svc.observe) {
        let o = svc.observe(self, (x as {value: unknown}).value, input)
        if (isEffect(o)) o = R.run(o, now)
        const mine = r.decode(st) as Record<string, unknown>, want = svc.view ? svc.view(mine, input) : mine
        for (const [k, v] of Object.entries(o as Record<string, unknown>)) if (JSON.stringify(v) !== JSON.stringify(want[k])) return {checked, failure: `${at}: the service's ${k} is ${JSON.stringify(v)}, the rule's ${JSON.stringify(want[k])}`}
      }
      checked++
    }
  }
  return {checked}
}

// A Schema's kind (its type side, 3.x or 4.x): a struct a record, string literals a choice, a tagged union of structs a
// variant on `_tag`, integers int (nat where at least 0), Boolean, String, `X | null` and optional fields a maybe, a
// Schema.Class its fields. A number that may be fractional, and any other Schema, is refused with the path to it.
// 3.x's AST nodes by 4.x's names:
const TAGS: Record<string, string> = {NumberKeyword: 'Number', BooleanKeyword: 'Boolean', StringKeyword: 'String', TypeLiteral: 'Objects', UndefinedKeyword: 'Undefined'}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function fromSchema(schema: {ast: unknown, fields?: Record<string, {ast: unknown}>}): Kind<any> {
  type Ast = Mod
  const fail = (path: string, what: string): never => { throw new Error(`fromSchema: ${path || 'the schema'} is ${what}`) }
  const tagOf = (a: Ast): string => TAGS[a?._tag] ?? a?._tag
  const ann = (a: Ast, id: string) => { const k = Object.getOwnPropertySymbols(a.annotations ?? {}).find(x => x.description === id); return k ? a.annotations[k] : undefined }
  const base = (a: Ast): Ast => (a._tag === 'Refinement' ? base(a.from) : a)
  // An integer: 4.x's checks on Number (isInt, a minimum), 3.x's Refinements down to NumberKeyword (Int, a JSON Schema minimum).
  const num = (a: Ast, path: string): Kind<unknown> => {
    let int = false, min = -Infinity
    for (let x = a; x; x = x._tag === 'Refinement' ? x.from : undefined) {
      const js = ann(x, 'effect/annotation/JSONSchema') as {type?: string, minimum?: number} | undefined
      for (const c of [...(x.checks ?? []).map((c: Ast) => c.annotations ?? {}).map((an: Ast) => ({int: an.representation?.id === 'effect/schema/isInt' || an.arbitraryConstraint?.number?.isInteger, min: an.arbitraryConstraint?.minimum})),
        {int: js?.type === 'integer' || ann(x, 'effect/annotation/SchemaId')?.description === 'effect/SchemaId/Int', min: js?.minimum}]) { int ||= !!c.int; if (typeof c.min === 'number') min = Math.max(min, c.min) }
    }
    return int ? (min >= 0 ? dsl.nat : dsl.int) : fail(path, 'a number that may be fractional (an integer schema, Schema.Int, is read)')
  }
  const props = (a: Ast) => a.propertySignatures as {name: PropertyKey, type: Ast, isOptional?: boolean, context?: {isOptional?: boolean}}[]
  const go = (a: Ast, path: string): Kind<unknown> => {
    const tag = tagOf(a)
    if (tag === 'Transformation') return go(a.to, path)
    if (tag === 'Number' || (tag === 'Refinement' && tagOf(base(a)) === 'Number')) return num(a, path)
    if (tag === 'Refinement') return go(a.from, path)
    if (tag === 'Boolean') return dsl.bool
    if (tag === 'String') return dsl.str()
    if (tag === 'Literal') return typeof a.literal === 'string' ? dsl.oneOf(a.literal) : fail(path, `the literal ${String(a.literal)} (string literals are read)`)
    if (tag === 'Objects') { if (a.indexSignatures?.length) fail(path, 'a record with an index signature'); return dsl.record(fieldsOf(a, path, false) as never) }
    if (tag !== 'Union') return fail(path, `a ${a?._tag} schema (structs, literals, tagged unions, integers, booleans and strings are read)`)
    const types = a.types as Ast[], missing = types.filter(t => ['Null', 'Undefined'].includes(tagOf(t)) || (t._tag === 'Literal' && t.literal === null)), rest = types.filter(t => !missing.includes(t))
    const caseOf = (t: Ast) => { const p = tagOf(t) === 'Objects' ? props(t).find(x => x.name === '_tag') : undefined; return p?.type._tag === 'Literal' && typeof p.type.literal === 'string' ? p.type.literal as string : undefined }
    if (missing.length && rest.length === 1) return dsl.maybe(go(rest[0]!, path))
    if (rest.every(t => t._tag === 'Literal' && typeof t.literal === 'string')) return dsl.oneOf(...rest.map(t => t.literal as string))
    if (!missing.length && rest.every(caseOf)) return dsl.variant(Object.fromEntries(rest.map(t => [caseOf(t)!, fieldsOf(t, path, true)])) as never, {tag: '_tag'})
    return fail(path, 'a union other than of string literals, of structs tagged by _tag, or with null')
  }
  const fieldsOf = (a: Ast, path: string, tagged: boolean): Record<string, Kind<unknown>> => Object.fromEntries(props(a).filter(p => !(tagged && p.name === '_tag')).map(p => {
    const k = go(p.type, `${path ? `${path}.` : ''}${String(p.name)}`)
    return [String(p.name), (p.isOptional || p.context?.isOptional) && !('of' in k) ? dsl.maybe(k) : k]
  }))
  const ast = schema.ast as Ast
  return schema.fields && tagOf(ast) !== 'Objects' ? dsl.record(Object.fromEntries(Object.entries(schema.fields).map(([f, x]) => [f, go(x.ast as Ast, f)])) as never) : go(ast, '')
}
