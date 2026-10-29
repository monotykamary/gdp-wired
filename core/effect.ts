// Effect (the `effect` package, 3.x and 4.x) as a front end (`gdp-wired/effect`): a service whose make effect creates
// Refs and returns an object of methods, read as core/extract.ts reads a factory's object of functions
// (core/extract-shapes.ts). Each Ref (Ref, SynchronizedRef, SubscriptionRef, 4.x's TxRef) is a field of the state, each
// method an event, its success value `<method>_result`, a failure (Effect.fail, Effect.die, `yield* new E(...)`) the
// step's refusal, Clock.currentTimeMillis an input, a Semaphore of 1's withPermits(1) a lock; each method is one step
// (true where calls don't interleave). What is read and refused, with the reasons, is in
// skills/gdp-wired/references/writing-rules.md ("Effect services") and research/effect/README.md.
//
//   const x = extractEffect(code, {file: 'limiter.ts', entry: 'make', effect: await import('effect')})
//
// The check runs the code on the Effect given: the service made, and each request run, by Effect.runSyncExit with a
// Clock fixed at the request's time (4.x's TestClock.setTime yields to its scheduler, which runSync can't), every Ref
// read after it. `conforms(rule, service)` runs a rule written by hand beside a running service; `fromSchema(schema)` is
// a Schema's kind.
import ts from 'typescript'
import * as dsl from './dsl.ts'
import type {Kind, Rule} from './dsl.ts'
import {type Rand, interpret, seeded} from './machine.ts'
import {allowed} from './watch.ts'
import * as I from './extract-ir.ts'
import {type Exec, type Path, Refusal, type Setup, type V, bare as strip, impure, memberName, placed, refuse, shapeOf, text} from './extract-read.ts'
import {type FactoryOf, readFactory} from './extract-shapes.ts'
import {type ExtractOptions, type Extraction, fromModel} from './extract.ts'
import {check} from './extract-check.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Mod = Record<string, any>
export type EffectOptions = ExtractOptions & {
  // The `effect` package the code is written for (import * as effect from 'effect'): the check runs the code on it.
  effect: Mod,
  // Other modules the code imports, for the check (by their specifier).
  modules?: Record<string, unknown>,
}
const REFS = new Set(['Ref', 'SynchronizedRef', 'SubscriptionRef', 'TxRef']), MAKES = ['make', 'makeUnsafe', 'unsafeMake']
const STM = (api: string) => `${api}: STM (v3) is not read (a Ref, SynchronizedRef, or v4's TxRef is)`, MATCH = (x: string) => `${x}: a matcher (write the dispatch as a switch on _tag, or ifs)`
// Where on a path the step has changed a Ref so far (a condition in the heap, so merges and helpers carry it).
const CHANGED = '$changed'
const changedOn = (p: Path): I.B => { const o = p.heap.get(CHANGED); return o?.k === 'alias' && o.to.t === 'bool' ? o.to.e : I.F }
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
const genOf = (s: Setup, e: ts.Expression): ts.FunctionExpression | undefined => {
  if (callOf(s, e) !== 'Effect.gen') return undefined
  const args = (strip(e) as ts.CallExpression).arguments, g = args.at(-1)
  if (args.length !== 1) refuse(e, 'Effect.gen with a this (a generator of one function is read)')
  return g && ts.isFunctionExpression(g) && g.asteriskToken ? g : refuse(e, 'Effect.gen of other than a function*')
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
        if (m === 'TRef' || m === 'STM') return refuse(d, STM(api))
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
  const fail = (ex: Exec, at: ts.Node, q: Path): [V, Path] => {
    if (!ex.known(q, I.not(changedOn(q)))) refuse(at, `fails after writing ${q.wrote.join(', ')}: a Ref keeps what was written (a rule's refusal leaves the state as it was)`)
    ex.throws.push({pc: q.pc})
    return [undef, {...q, pc: [...q.pc, I.F]}]
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
      if (api === 'Effect.void' || api === 'Effect.unit') return [eff(q => [undef, q]), p]
      if (api === 'Clock.currentTimeMillis') return [eff(q => ex.now(e, q)), p]
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
      if (callOf(s, head)?.startsWith('Match.')) return refuse(head, MATCH(text(head)))
      for (const a of e.arguments) if (!ANNOTATIONS.has(callOf(s, a) ?? '')) return refuse(a, `${text(a)} in a pipe (a combinator's effect isn't read: write the step in Effect.gen)`)
      return ex.ev(callee.expression, p)
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
    if (m === 'Effect') {
      if (op === 'gen') return [body(ex, genOf(s, e)!, e, p.locals), p]
      if (op === 'succeed') { const [v, q] = ex.ev(one ?? refuse(e, 'Effect.succeed()'), p); return [eff(r => [v, r]), q] }
      if (op === 'sync') return [body(ex, fnOf(s, one ?? refuse(e, 'Effect.sync()')) ?? refuse(e, 'Effect.sync of other than a function written here'), e, p.locals), p]
      if (FAILS.has(op)) return e.arguments.some(effectful) ? refuse(e, `Effect.${op} of a value that has effects`) : [eff(q => fail(ex, e, q)), p]
      if (LOGS.has(op)) {
        if (e.arguments.some(impure)) return refuse(e, `Effect.${op} of values that have effects`)
        s.notes.add('Effect.log and span annotations are left out (they write nothing the rule keeps)')
        return [eff(q => [undef, q]), p]
      }
      return refuse(e, op === 'fn' || op === 'fnUntraced' ? `Effect.${op} as a value inside a step (a method or a helper of the service is read)` : `Effect.${op} (Effect.gen, Effect.fn bodies, succeed, sync, fail, die, void and log are read; the effect of ${op} isn't)`)
    }
    if (m === 'Match') return refuse(e, MATCH(api!))
    if (m === 'STM' || m === 'TRef') return refuse(e, STM(api!))
    if (m === 'Semaphore') return refuse(e, `${api} (a Semaphore of 1 made by the service, as a lock, is read)`)
    return undefined
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
  const clock = Object.create(Effect.runSync(v4 ? Effect.clockWith((c: unknown) => Effect.succeed(c)) : Effect.clock), {[unsafe('Millis')]: {value: () => now}, currentTimeMillis: {value: Effect.sync(() => now)}, [unsafe('Nanos')]: {value: ns}, currentTimeNanos: {value: Effect.sync(ns)}})
  const exit = (eff: unknown, t: number): {ok: true, value: unknown} | {ok: false, error: string} => {
    if (!Effect.isEffect(eff)) return {ok: false, error: `not an effect: ${String(eff).slice(0, 60)}`}
    now = t
    const x = Effect.runSyncExit(v4 ? Effect.provideService(eff, Clock.Clock, clock) : Effect.withClock(eff, clock))
    return Exit.isSuccess(x) ? {ok: true, value: x.value} : {ok: false, error: String(Cause.pretty(x.cause)).split('\n')[0]!}
  }
  const run = (eff: unknown, t = now) => { const x = exit(eff, t); if (!x.ok) throw new Error(x.error); return x.value }
  return {run, exit, get: (mod, ref) => run(E[mod].get(ref)), set: (mod, ref, v) => run(E[mod].set(ref, v))}
}

export function extractEffect(code: string, opts: EffectOptions): Extraction {
  const file = opts.file ?? 'input.ts', E = opts.effect
  let m
  try { m = readFactory(code, placed(file), opts, s => factoryOf(s, opts.entry)); m.file = file } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  // The modules the code imports, by specifier (effect, effect/<Module>), and the check's runner.
  const model = m, modules = {effect: E, ...Object.fromEntries(Object.entries(E).map(([k, x]) => [`effect/${k}`, x])), 'gdp-wired:effect': runner(E), ...opts.modules}
  return fromModel(model, file, opts.domains, [], (rule, sorts) => check(code, file, model, rule, sorts, {...opts.check, modules, ...(opts.files ? {files: opts.files} : {}), ...(opts.domains ? {given: opts.domains} : {})}))
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
