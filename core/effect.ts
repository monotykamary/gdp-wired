// Effect (effect-ts, the `effect` package, 3.x and 4.x) as a front end (`gdp-wired/effect`). A service written in Effect
// keeps its state in Refs its make effect creates, and each method is an effect over them:
//
//   export const make = Effect.gen(function* () {
//     const tokens = yield* Ref.make(10)
//     const take = Effect.fn('take')(function* (n: number) {
//       const t = yield* Ref.get(tokens)
//       if (n > t) return yield* new RateLimited({n})
//       yield* Ref.set(tokens, t - n)
//     })
//     return {take}
//   })
//
//   const x = extractEffect(code, {file: 'limiter.ts', entry: 'make', effect: await import('effect')})
//   proveRule(x.rule, [x.rule.law('within capacity', ({tokens}) => tokens.atMost(10))])
//
// The service is read as core/extract.ts reads a factory's object of functions: each Ref a field of the state (its type
// the Ref's), each method an event, its arguments the request, its success value kept as `<method>_result`, a typed
// failure (Effect.fail, a yielded error, a defect) the rule's refusal, and Clock.currentTimeMillis an input (as Date.now()).
// The make effect is `Effect.gen(...)`, a function returning one, `Effect.fn(...)(function* (...) {...})`, `Layer.effect`
// or `Layer.scoped` of one, or the `make` (v4 Context.Service) or `effect` (v3 Effect.Service) option of a service class;
// it returns its object as `{...}`, `Tag.of({...})` or `{...} satisfies T`. Inside a method: `yield*` of a Ref's get, set,
// update, modify, updateAndGet, getAndUpdate, getAndSet, setAndGet (and SynchronizedRef's and SubscriptionRef's
// *Effect forms), of Ref, SynchronizedRef, SubscriptionRef and v4's TxRef alike; Effect.gen, Effect.fn and
// Effect.fnUntraced bodies, helpers of the same files, Effect.succeed, Effect.sync, Effect.void, Effect.fail,
// Effect.die, a yielded error (`yield* new E(...)`), Effect.log*, a Semaphore of 1's withPermits(1) (one call at a
// time); the functions given to update and modify are plain TypeScript in the extractor's subset (a Map copied with
// new Map(m) and set, records spread). Each method is one step: where calls interleave (two fibers, no lock), a method
// that reads a Ref and writes it in two operations is not one step, and the rule is of calls one at a time.
//
// Refused, with the reason where it is: a failure after a Ref is written (the Ref keeps it; a rule's refusal leaves the
// state as it was), pipes of combinators (catch, retry, timeout, forkDaemon, ...: their effects aren't read), Match
// (write the dispatch as a switch or an if), Data.TaggedEnum or Schema unions of records as state (a union of records),
// STM's TRef (v3), Refs held in values or made in a step, services yielded inside a method (their answers come from
// outside), and everything core/extract.ts refuses. The rule is checked by running the real code through the Effect
// runtime given (`effect`): the service made by Effect.runSyncExit, each request run the same way with the clock fixed at
// the request's time (a Clock provided: v4's TestClock.setTime yields to its scheduler, which runSync can't), every Ref
// read after it, its result and its failure compared with the rule's (core/extract-check.ts).
//
// `conforms(rule, service)` runs a rule written by hand beside a running service (its own Semaphore, a store), each
// request and failure compared, and the service's state where `observe` reads it; `fromSchema(schema)` is the kind of a
// Schema (a struct, literals, tagged unions, integers), so laws can be written over a project's Schema types.
import ts from 'typescript'
import * as dsl from './dsl.ts'
import type {Kind, Rule} from './dsl.ts'
import {type Rand, interpret, seeded} from './machine.ts'
import {allowed} from './watch.ts'
import * as I from './extract-ir.ts'
import {type Exec, type Path, Refusal, type Setup, type V, impure, memberName, placed, shapeOf} from './extract-read.ts'
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

const where = (n: ts.Node) => { const sf = n.getSourceFile(), {line, character} = sf.getLineAndCharacterOfPosition(n.getStart()); return `${sf.fileName.split('/').pop()}:${line + 1}:${character + 1}` }
const refuse = (n: ts.Node, what: string): never => { throw new Refusal(where(n), what) }
const strip = (e: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) || ts.isNonNullExpression(e) ? strip(e.expression) : e)
const text = (n: ts.Node) => n.getText().replace(/\s+/g, ' ').slice(0, 60)
const REFS = new Set(['Ref', 'SynchronizedRef', 'SubscriptionRef', 'TxRef'])

// --- the reader -----------------------------------------------------------------------------------------------------
// The module of Effect a name is (Ref for `import * as Ref from 'effect/Ref'`, `import {Ref} from 'effect'`, or
// `E.Ref` of `import * as E from 'effect'`), and the member read of it.
function apiOf(s: Setup, e: ts.Expression): [string, string] | undefined {
  e = strip(e)
  if (!ts.isPropertyAccessExpression(e)) return undefined
  const mod = (x: ts.Expression): string | undefined => {
    x = strip(x)
    if (ts.isPropertyAccessExpression(x)) return mod(x.expression) === '' ? memberName(x.name) : undefined
    if (!ts.isIdentifier(x)) return undefined
    const d = s.checker.getSymbolAtLocation(x)?.declarations?.[0]
    const spec = (n: ts.Node | undefined): string | undefined => { while (n && !ts.isImportDeclaration(n)) n = n.parent; return n && ts.isStringLiteral(n.moduleSpecifier) ? n.moduleSpecifier.text : undefined }
    if (d && ts.isNamespaceImport(d)) { const m = spec(d); return m === 'effect' ? '' : m?.match(/^effect\/(\w+)$/)?.[1] }
    if (d && ts.isImportSpecifier(d) && spec(d) === 'effect') return (d.propertyName ?? d.name).text
    return undefined
  }
  const m = mod(e.expression)
  return m ? [m, memberName(e.name)] : undefined
}
// A function an Effect service writes: Effect.fn('name')(function* ...), Effect.fn(function* ...),
// Effect.fnUntraced(function* ...), or an arrow or function.
function fnOf(s: Setup, e: ts.Expression): ts.FunctionLikeDeclaration | undefined {
  e = strip(e)
  if (ts.isArrowFunction(e) || ts.isFunctionExpression(e)) return e
  if (!ts.isCallExpression(e)) return undefined
  const head = ts.isCallExpression(e.expression) ? apiOf(s, e.expression.expression) : apiOf(s, e.expression)
  if (head?.[0] !== 'Effect' || (head[1] !== 'fn' && head[1] !== 'fnUntraced')) return undefined
  const g = e.arguments[0] && strip(e.arguments[0])
  if (!g || !ts.isFunctionExpression(g) || !g.asteriskToken) return undefined
  if (e.arguments.length > 1) refuse(e.arguments[1]!, `Effect.${head[1]} with combinators after its body (their effects aren't read)`)
  return g
}
const genOf = (s: Setup, e: ts.Expression): ts.FunctionExpression | undefined => {
  e = strip(e)
  if (!ts.isCallExpression(e) || apiOf(s, e.expression)?.join('.') !== 'Effect.gen') return undefined
  const g = e.arguments.at(-1)
  if (e.arguments.length !== 1) refuse(e, 'Effect.gen with a this (a generator of one function is read)')
  return g && ts.isFunctionExpression(g) && g.asteriskToken ? g : refuse(e, 'Effect.gen of other than a function*')
}
// A type's type argument: Ref<A>'s A, Effect<A, E, R>'s A, Generator<Y, R, N>'s R.
const argOf = (s: Setup, t: ts.Type, i: number): ts.Type | undefined => (t.aliasTypeArguments ?? (t.flags & ts.TypeFlags.Object ? s.checker.getTypeArguments(t as ts.TypeReference) : undefined))?.[i]

// The service's make: the generator whose statements make the Refs and return the object, its params, and how the
// check makes the service (by calling the entry, or the effect captured where it is written).
function factoryOf(s: Setup, entry: string): FactoryOf {
  const [name, member] = entry.split('.')
  let decl: ts.Node | undefined
  for (const st of s.sf.statements) {
    if ((ts.isFunctionDeclaration(st) || ts.isClassDeclaration(st)) && st.name?.text === name) decl = st
    if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === name) decl = d
  }
  if (!decl) return refuse(s.sf.statements[0] ?? s.sf, `no ${name} in the file`)
  // The make effect, as written (a class's option, a static member, a variable's value), followed through Layer.effect
  // and names of the same file.
  let e: ts.Expression | undefined, at: ts.Node = decl
  if (ts.isClassDeclaration(decl)) {
    if (member) { const m = decl.members.find(x => ts.isPropertyDeclaration(x) && x.name && memberName(x.name) === member) as ts.PropertyDeclaration | undefined; e = m?.initializer }
    else {
      const base = decl.heritageClauses?.[0]?.types[0]?.expression, opts = base && ts.isCallExpression(base) ? base.arguments[1] : undefined
      const o = opts && strip(opts)
      if (o && ts.isObjectLiteralExpression(o)) e = (o.properties.find(p => ts.isPropertyAssignment(p) && ['make', 'effect', 'scoped'].includes(memberName(p.name))) as ts.PropertyAssignment | undefined)?.initializer
    }
  } else if (ts.isVariableDeclaration(decl)) e = decl.initializer
  else if (ts.isFunctionDeclaration(decl)) {
    const last = decl.body?.statements.at(-1)
    return fromFunction(decl, last && ts.isReturnStatement(last) ? last.expression : undefined)
  }
  for (let i = 0; e && i < 8; i++) {
    e = strip(e)
    const api = ts.isCallExpression(e) ? apiOf(s, e.expression) : undefined
    if (api?.[0] === 'Layer' && (api[1] === 'effect' || api[1] === 'scoped') && ts.isCallExpression(e)) { e = e.arguments[1]; continue }
    if (ts.isIdentifier(e)) { const d = s.checker.getSymbolAtLocation(e)?.valueDeclaration; if (d && ts.isVariableDeclaration(d) && d.getSourceFile() === s.sf) { e = d.initializer; at = d; continue } }
    break
  }
  if (!e) return refuse(at, `${entry}: no make effect (an Effect.gen, a function returning one, Effect.fn, or Layer.effect of one)`)
  const gen = genOf(s, e)
  if (gen) return made(gen, [], e)
  const f = fnOf(s, e)
  if (f && ts.isFunctionExpression(f) && f.asteriskToken) return made(f, f.parameters)
  if (f) return fromFunction(f, ts.isBlock(f.body!) ? (() => { const last = (f.body as ts.Block).statements.at(-1); return last && ts.isReturnStatement(last) ? last.expression : undefined })() : f.body as ts.Expression)
  return refuse(e, `${entry}: ${text(e)} is no make effect the reader reads (an Effect.gen, a function returning one, Effect.fn, or Layer.effect of one)`)

  function fromFunction(f: ts.FunctionLikeDeclaration, ret: ts.Expression | undefined): FactoryOf {
    const g = ret && genOf(s, ret)
    if (!g || (ts.isBlock(f.body!) && f.body.statements.length > 1)) return refuse(f, `${entry} returns no Effect.gen (a function whose body is the make effect is read)`)
    return made(g, f.parameters)
  }
  // The make effect at `capture` (a value, not a function): captured where the code makes it, so the check runs it.
  function made(fn: ts.FunctionExpression, params: readonly ts.ParameterDeclaration[], capture?: ts.Expression): FactoryOf {
    const ret = fn.body.statements.at(-1)
    let o = ret && ts.isReturnStatement(ret) && ret.expression ? strip(ret.expression) : undefined
    if (o && ts.isCallExpression(o) && ts.isPropertyAccessExpression(o.expression) && memberName(o.expression.name) === 'of' && o.arguments.length === 1) o = strip(o.arguments[0]!)
    if (!o || !ts.isObjectLiteralExpression(o)) return refuse(fn, `${entry}'s make effect returns no object of methods (\`return {...}\` or \`return Tag.of({...})\`)`)
    const refs = new Map<string, string>(), locks = new Set<ts.Node>()
    s.effect = hook(s, refs, locks)
    s.notes.add(`${entry} is an Effect service: its state is its Refs, each method an event, a failure the step's refusal; each method is one step, which holds where calls don't interleave (one at a time, or under a Semaphore of 1)`)
    const R = 'require("gdp-wired:effect")'
    const make = capture ? 'globalThis.__gdpMake' : `__gdp[${JSON.stringify(entry)}]`
    return {
      fn, params, obj: o,
      decl: d => {
        const init = d.initializer && strip(d.initializer)
        if (!init) return undefined
        if (fnOf(s, init)) return 'helper'
        const call = ts.isYieldExpression(init) && init.expression ? strip(init.expression) : init
        const api = ts.isCallExpression(call) ? apiOf(s, call.expression) : undefined
        if (api && ts.isCallExpression(call) && REFS.has(api[0]) && ['make', 'makeUnsafe', 'unsafeMake'].includes(api[1])) {
          if (!call.arguments[0]) return refuse(call, `${api.join('.')}() with no start`)
          const t = argOf(s, s.checker.getTypeAtLocation(d.name), 0) ?? refuse(d, `${text(d)}: no type for the Ref's value`)
          refs.set((d.name as ts.Identifier).text, api[0])
          return {shape: shapeOf(t, s.checker, d), init: call.arguments[0]}
        }
        if (api?.[0] === 'TRef' || api?.[0] === 'STM') return refuse(d, `${api.join('.')}: STM (v3) is not read (a Ref, SynchronizedRef, or v4's TxRef is)`)
        if (api?.[0] === 'Semaphore' || (api?.[0] === 'Effect' && /^(unsafeM|m)akeSemaphore$/.test(api[1]))) {
          const n = ts.isCallExpression(call) ? call.arguments[0] : undefined
          if (!n || !ts.isNumericLiteral(n) || n.text !== '1') return refuse(d, `${text(d)}: a Semaphore of other than 1 permit (one of 1 is read as a lock)`)
          locks.add(d); return 'helper'
        }
        if (ts.isYieldExpression(init)) return refuse(d, `${(d.name as ts.Identifier).text}: ${text(init)} run while the service is made (its value comes from outside the Refs read)`)
        return undefined
      },
      fnOf: x => fnOf(s, x),
      result: f => {
        const t = s.checker.getReturnTypeOfSignature(s.checker.getSignatureFromDeclaration(f)!)
        return argOf(s, t, f.asteriskToken ? 1 : 0) ?? refuse(f, `${text(f)}: no type for its result (${s.checker.typeToString(t)})`)
      },
      run: (ex, v, at2, p) => (v.t === 'eff' ? v.run(p) : refuse(at2, `${text(at2)} returns a ${v.t} where a method returns an effect`)),
      get: n => (refs.has(n) ? `${n}: ${R}.get(${JSON.stringify(refs.get(n))}, ${n})` : undefined),
      set: n => (refs.has(n) ? `${R}.set(${JSON.stringify(refs.get(n))}, ${n}, __s.${n});` : undefined),
      calls: `const __R = ${R}; __gdp.$new = function (...args) { const f = ${make}; return __R.run(typeof f === 'function' ? f(...args) : f, __now()) }; __gdp.$method = function (name, args) { const f = this[name]; return __R.run(typeof f === 'function' ? f(...args) : f, __now()) }; __gdp.$get = function () { return this.__gdpGet() }; __gdp.$at = function (fields, args) { const o = __gdp.$new(...args); o.__gdpSet(fields); return o }`,
      ...(capture ? {extra: [[capture.getStart(), '(globalThis.__gdpMake = '], [capture.end, ')']] as [number, string][]} : {}),
    }
  }
}

// Effect's expressions in a step: yield* runs an effect; Ref's, Effect's and Clock's calls make one (an `eff` value, run
// where it is yielded, so a helper or a branch may make it and another place run it).
function hook(s: Setup, refs: Map<string, string>, locks: Set<ts.Node>) {
  const eff = (run: (p: Path) => [V, Path]): V => ({t: 'eff', run})
  const undef: V = {t: 'undef'}
  return (ex: Exec, e: ts.Expression, p: Path): [V, Path] | undefined => {
    if (ts.isYieldExpression(e)) {
      if (!e.asteriskToken || !e.expression) return refuse(e, 'yield without * (Effect.gen runs an effect with yield*)')
      const x = strip(e.expression)
      // A yielded error (Schema.TaggedError, Data.TaggedError): its failure.
      if (ts.isNewExpression(x)) return [undef, fail(ex, x, p)]
      const [v, q] = ex.ev(x, p)
      return v.t === 'eff' ? v.run(q) : refuse(x, `yield* of ${text(x)}, not an effect the reader runs (a ${v.t})`)
    }
    if (ts.isPropertyAccessExpression(e)) {
      const api = apiOf(s, e)?.join('.')
      if (api === 'Effect.void' || api === 'Effect.unit') return [eff(q => [undef, q]), p]
      if (api === 'Clock.currentTimeMillis') return [eff(q => ex.now(e, q)), p]
      if (api?.startsWith('Clock.')) return refuse(e, `${api} (Clock.currentTimeMillis is read, as an input)`)
      return undefined
    }
    if (!ts.isCallExpression(e)) return undefined
    const callee = strip(e.expression), api = apiOf(s, callee)
    // A lock: sem.withPermits(1)(effect), sem.withPermit(effect), Semaphore.withPermits(sem, 1)(effect).
    const lockOf = (x: ts.Expression) => { const d = ts.isIdentifier(x) ? s.checker.getSymbolAtLocation(x)?.valueDeclaration : undefined; return !!d && locks.has(d) }
    if (ts.isPropertyAccessExpression(callee) && memberName(callee.name) === 'withPermit' && lockOf(callee.expression) && e.arguments.length === 1) return ex.ev(e.arguments[0]!, p)
    if (ts.isCallExpression(callee) && e.arguments.length === 1) {
      const inner = strip(callee.expression), one = callee.arguments.at(-1)
      const sem = ts.isPropertyAccessExpression(inner) && memberName(inner.name) === 'withPermits' ? (lockOf(inner.expression) ? inner.expression : apiOf(s, inner)?.join('.') === 'Semaphore.withPermits' ? callee.arguments[0] : undefined) : undefined
      if (sem && lockOf(sem)) return one && ts.isNumericLiteral(one) && one.text === '1' ? ex.ev(e.arguments[0]!, p) : refuse(e, 'withPermits of other than 1 (a Semaphore of 1 is a lock; more permits let calls interleave)')
    }
    // x.pipe(...): only annotations (a span, a log annotation) are read through.
    if (ts.isPropertyAccessExpression(callee) && memberName(callee.name) === 'pipe' && !api) {
      for (const a of e.arguments) { const k = ts.isCallExpression(strip(a)) ? apiOf(s, (strip(a) as ts.CallExpression).expression)?.join('.') : undefined; if (!k || !['Effect.withSpan', 'Effect.withLogSpan', 'Effect.annotateLogs', 'Effect.annotateSpans'].includes(k)) return refuse(a, `${text(a)} in a pipe (a combinator's effect isn't read: write the step in Effect.gen)`) }
      return ex.ev(callee.expression, p)
    }
    // A helper of the same files written with Effect.fn: its body run where it is yielded.
    if (ts.isIdentifier(callee)) {
      const d = s.checker.getSymbolAtLocation(callee)?.valueDeclaration
      const f = d && ts.isVariableDeclaration(d) && d.initializer && s.ours(d.getSourceFile()) ? fnOf(s, d.initializer) : undefined
      if (f?.asteriskToken) { const [args, q] = argsOf(ex, e.arguments, p); return [eff(r => ex.inline({decl: f}, args, e, r)), q] }
      return undefined
    }
    if (!api) return undefined
    const [m, op] = api
    if (REFS.has(m)) return refOp(ex, e, m, op, p)
    if (m === 'Effect') {
      const arg = e.arguments[0]
      switch (op) {
        case 'gen': { const g = genOf(s, e)!; const locals = p.locals; return [eff(q => ex.inline({decl: g}, [], e, q, locals)), p] }
        case 'succeed': { const [v, q] = ex.ev(arg ?? refuse(e, 'Effect.succeed()'), p); return [eff(r => [v, r]), q] }
        case 'sync': { const f = fnOf(s, arg ?? refuse(e, 'Effect.sync()')) ?? refuse(e, 'Effect.sync of other than a function written here'); const locals = p.locals; return [eff(q => ex.inline({decl: f}, [], e, q, locals)), p] }
        case 'fail': case 'failSync': case 'die': case 'dieMessage':
          if (e.arguments.some(impure)) return refuse(e, `Effect.${op} of a value that has effects`)
          return [eff(q => [undef, fail(ex, e, q)]), p]
        case 'log': case 'logTrace': case 'logDebug': case 'logInfo': case 'logWarning': case 'logError': case 'logFatal': case 'annotateCurrentSpan':
          if (e.arguments.some(impure)) return refuse(e, `Effect.${op} of values that have effects`)
          s.notes.add('Effect.log and span annotations are left out (they write nothing the rule keeps)')
          return [eff(q => [undef, q]), p]
        case 'fn': case 'fnUntraced': return refuse(e, `Effect.${op} as a value inside a step (a method or a helper of the service is read)`)
        default: return refuse(e, `Effect.${op} (Effect.gen, Effect.fn bodies, succeed, sync, fail, die, void and log are read; the effect of ${op} isn't)`)
      }
    }
    if (m === 'Match') return refuse(e, `Match.${op}: a matcher (write the dispatch as a switch on _tag, or ifs)`)
    if (m === 'STM' || m === 'TRef') return refuse(e, `${m}.${op}: STM (v3) is not read (a Ref, SynchronizedRef, or v4's TxRef is)`)
    if (m === 'Semaphore') return refuse(e, `Semaphore.${op} (a Semaphore of 1 made by the service, as a lock, is read)`)
    return undefined
  }
  function argsOf(ex: Exec, xs: readonly ts.Expression[], p: Path): [V[], Path] {
    const out: V[] = []
    let q = p
    for (const x of xs) { const [v, q2] = ex.ev(x, q); out.push(v); q = q2 }
    return [out, q]
  }
  // A failure: the step refused where it is reached; after a Ref is written, the Ref keeps the write.
  function fail(ex: Exec, at: ts.Node, q: Path): Path {
    if (q.wrote.length) refuse(at, `fails after writing ${q.wrote.join(', ')}: a Ref keeps what was written (a rule's refusal leaves the state as it was)`)
    ex.throws.push({pc: q.pc})
    return {...q, pc: [...q.pc, I.F]}
  }
  // Ref.op(ref, ...): the ref a Ref the service made (by its name), its value the state's field.
  function refOp(ex: Exec, e: ts.CallExpression, m: string, op: string, p: Path): [V, Path] {
    const r = e.arguments[0] && strip(e.arguments[0])
    if (['make', 'makeUnsafe', 'unsafeMake'].includes(op)) return refuse(e, `${m}.${op} in a step (each call would make a new Ref: the service's Refs are made by its make effect)`)
    if (!r) return refuse(e, `${m}.${op} with no Ref`)
    const name = ts.isIdentifier(r) && refs.has(r.text) && s.closure?.has(s.checker.getSymbolAtLocation(r)?.valueDeclaration as ts.Node) ? r.text : refuse(r, `${text(r)}: a Ref other than one the service's make effect makes (a Ref held in a value, or given to it)`)
    const self: V = {t: 'ref', id: 'this'}
    const cur = (q: Path) => ex.field(self, name, r, q)
    const put = (v: V, q: Path): Path => { const [w, q2] = whole(ex, v, q, r); return ex.writeField(self, name, w, q2, r) }
    const locals = p.locals
    const apply = (args: V[], q: Path): [V, Path] => {
      const f = e.arguments[1] ?? refuse(e, `${m}.${op} with no function`)
      const fn = fnOf(s, f) ?? (ts.isIdentifier(f) ? (() => { const d = s.checker.getSymbolAtLocation(f)?.valueDeclaration; return d && ts.isFunctionDeclaration(d) && s.ours(d.getSourceFile()) ? d : undefined })() : undefined)
      if (!fn || fn.asteriskToken) return refuse(f, `${m}.${op} of other than a function written here`)
      const [v, q2] = ex.inline({decl: fn}, args, f, q, ts.isIdentifier(f) ? new Map() : locals)
      if (!/Effect$/.test(op)) return [v, q2]
      return v.t === 'eff' ? v.run(q2) : refuse(f, `${m}.${op}'s function returns other than an effect`)
    }
    const base = op.replace(/Effect$/, '')
    switch (base) {
      case 'get': return [eff(q => cur(q)), p]
      case 'set': case 'getAndSet': case 'setAndGet': {
        const [v, q0] = ex.ev(e.arguments[1] ?? refuse(e, `${m}.${op} with no value`), p)
        return [eff(q => { const [c, q1] = cur(q); return [base === 'set' ? undef : base === 'getAndSet' ? c : v, put(v, q1)] }), q0]
      }
      case 'update': case 'updateAndGet': case 'getAndUpdate':
        return [eff(q => { const [c, q1] = cur(q), [v, q2] = apply([c], q1); return [base === 'update' ? undef : base === 'updateAndGet' ? v : c, put(v, q2)] }), p]
      case 'modify':
        return [eff(q => {
          const [c, q1] = cur(q), [t, q2] = apply([c], q1)
          if (t.t !== 'tuple' || t.xs.length !== 2) return refuse(e.arguments[1]!, `${m}.${op}'s function returns other than [result, value]`)
          return [t.xs[0]!, put(t.xs[1]!, q2)]
        }), p]
      default: return refuse(e, `${m}.${op} (get, set, update, modify, updateAndGet, getAndUpdate, getAndSet and setAndGet are read)`)
    }
  }
}
// A Ref's new value, whole: two values by a condition (`cond ? next : current`) made one object (a map by cases, a
// record field by field), as a Ref's value is replaced and never written in place by another holder.
function whole(ex: Exec, v: V, q: Path, at: ts.Node): [V, Path] {
  if (v.t !== 'phi') return [v, q]
  const [a, qa] = whole(ex, v.a, q, at), [b, qb] = whole(ex, v.b, qa, at)
  const objOf = (x: V) => { let o = x.t === 'ref' ? qb.heap.get(x.id) : undefined; while (o?.k === 'alias' && o.to.t === 'ref') o = qb.heap.get(o.to.id); return o }
  const oa = objOf(a), ob = objOf(b), id = ex.id(oa?.k ?? 'obj')
  if (oa?.k === 'map' && ob?.k === 'map' && oa.base === ob.base) {
    const w = ex.mergeWrites(v.c, oa.decl, oa.w, ob.w, at)
    return [{t: 'ref', id}, {...qb, heap: new Map(qb.heap).set(id, {k: 'map', base: oa.base, decl: oa.decl, ...(w ? {w} : {}), origin: 'fresh', gen: Math.max(oa.gen, ob.gen) + 1})}]
  }
  if (oa?.k === 'rec' && ob?.k === 'rec' && !oa.lazy && !ob.lazy && [...oa.fields.keys()].sort().join() === [...ob.fields.keys()].sort().join()) {
    let r = qb
    const fields = new Map<string, V>()
    for (const [f, x] of oa.fields) { const [y, r2] = whole(ex, ex.phiV(v.c, x, ob.fields.get(f)!, at), r, at); fields.set(f, y); r = r2 }
    return [{t: 'ref', id}, {...r, heap: new Map(r.heap).set(id, {k: 'rec', fields, origin: 'fresh'})}]
  }
  return [{t: 'phi', c: v.c, a, b}, qb]
}

// --- running the code -----------------------------------------------------------------------------------------------
// Effects run synchronously on the Effect given (3.x or 4.x), the clock fixed at the request's time; a failure (a typed
// one, a defect, or an effect that would wait) is thrown, as the check reads a refusal.
export type Runner = {run: (eff: unknown, now?: number) => unknown, exit: (eff: unknown, now: number) => {ok: true, value: unknown} | {ok: false, error: string}, get: (mod: string, ref: unknown) => unknown, set: (mod: string, ref: unknown, v: unknown) => unknown}
export function runner(E: Mod): Runner {
  const {Effect, Exit, Cause, Clock} = E, v4 = 'TxRef' in E
  if (!Effect?.runSyncExit) throw new Error('effect: give the `effect` package itself (import * as effect from \'effect\')')
  let now = 0
  const base = v4 ? Effect.runSync(Effect.clockWith((c: unknown) => Effect.succeed(c))) : Effect.runSync(Effect.clock)
  const ms = {value: () => now}, ns = {value: () => BigInt(now) * 1_000_000n}, msE = {value: Effect.sync(() => now)}, nsE = {value: Effect.sync(() => BigInt(now) * 1_000_000n)}
  const clock = Object.create(base, v4 ? {currentTimeMillisUnsafe: ms, currentTimeMillis: msE, currentTimeNanosUnsafe: ns, currentTimeNanos: nsE} : {unsafeCurrentTimeMillis: ms, currentTimeMillis: msE, unsafeCurrentTimeNanos: ns, currentTimeNanos: nsE})
  const exit = (eff: unknown, t: number): {ok: true, value: unknown} | {ok: false, error: string} => {
    if (!Effect.isEffect(eff)) return {ok: false, error: `not an effect: ${String(eff).slice(0, 60)}`}
    now = t
    const x = Effect.runSyncExit(v4 ? Effect.provideService(eff, Clock.Clock, clock) : Effect.withClock(eff, clock))
    return Exit.isSuccess(x) ? {ok: true, value: x.value} : {ok: false, error: String(Cause.pretty(x.cause)).split('\n')[0]!}
  }
  const run = (eff: unknown, t = now) => { const x = exit(eff, t); if (!x.ok) throw new Error(x.error); return x.value }
  return {run, exit, get: (mod, ref) => run(E[mod].get(ref)), set: (mod, ref, v) => run(E[mod].set(ref, v))}
}
// The modules the code imports, by specifier: effect, effect/<Module> (and the check's runner).
const modulesOf = (E: Mod, R: Runner, extra: Record<string, unknown> = {}): Record<string, unknown> =>
  ({effect: E, ...Object.fromEntries(Object.entries(E).map(([k, m]) => [`effect/${k}`, m])), 'gdp-wired:effect': R, ...extra})

// --- the front end --------------------------------------------------------------------------------------------------
export function extractEffect(code: string, opts: EffectOptions): Extraction {
  const file = opts.file ?? 'input.ts', notes: string[] = []
  let model
  try { model = readFactory(code, placed(file), opts, s => factoryOf(s, opts.entry)); model.file = file } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  const m = model, modules = modulesOf(opts.effect, runner(opts.effect), opts.modules)
  return fromModel(m, file, opts.domains, notes, (rule, sorts) => check(code, file, m, rule, sorts, {...opts.check, modules, ...(opts.files ? {files: opts.files} : {}), ...(opts.domains ? {given: opts.domains} : {})}))
}

// A rule written by hand beside a running service: `runs` runs of `depth` requests drawn by `draw` (each the rule's
// inputs), each made of the service by `request` (an effect, run on the Effect given with the clock at the input named
// by `now`) and of the rule. They must fail together (the rule's assumption or step refuses where the effect fails),
// and after each step every field `observe` reads of the service (an effect or a value: its state in the rule's terms,
// and the request's result) must be the rule's.
export type Service<S> = {
  effect: Mod,
  make: (params: Record<string, unknown>) => unknown,
  request: (service: S, input: Record<string, unknown>) => unknown,
  observe?: (service: S, result: unknown, input: Record<string, unknown>) => unknown,
  now?: string,
}
export function conforms<S>(r: Rule, svc: Service<S>, opts: {draw: (rand: Rand) => Record<string, unknown>, params?: (rand: Rand) => Record<string, unknown>, runs?: number, depth?: number, seed?: number}): {checked: number, failure?: string} {
  const R = runner(svc.effect), rand = seeded(opts.seed ?? 1), g = r.compiled(), interp = interpret(r.machine)
  const same = (a: unknown, b: unknown): boolean => JSON.stringify(a) === JSON.stringify(b)
  let checked = 0
  for (let run = 0; run < (opts.runs ?? 100); run++) {
    const params = opts.params?.(rand) ?? {}, ps = r.encodeParams(params as never), made = R.exit(svc.make(params), 0)
    if (!made.ok) return {checked, failure: `the service with ${JSON.stringify(params)} fails to be made: ${made.error}`}
    const self = made.value as S, sent: string[] = []
    let st = g.init(ps)
    for (let d = 0; d < (opts.depth ?? 12); d++) {
      const input = opts.draw(rand), enc = r.encodeInput(input as never, params as never), now = svc.now ? Number(input[svc.now]) : 0
      sent.push(JSON.stringify(input))
      const at = () => `${params && Object.keys(params).length ? `with ${JSON.stringify(params)}, ` : ''}after ${sent.join(', ')}`
      let ok: boolean
      try { ok = allowed(r.machine, interp, ps, st, enc) && (g.step(ps, g.fork(st), enc), true) } catch { ok = false }
      const x = R.exit(svc.request(self, input), now)
      if (ok !== x.ok) return {checked, failure: `${at()}: the ${x.ok ? 'service takes the request' : `service fails (${(x as {error: string}).error})`}, the rule ${ok ? 'takes it' : 'refuses it'}`}
      if (!ok) continue
      st = g.step(ps, st, enc)
      if (svc.observe) {
        let o = svc.observe(self, (x as {value: unknown}).value, input)
        if (o && typeof o === 'object' && svc.effect.Effect.isEffect(o)) o = R.run(o, now)
        const mine = r.decode(st) as Record<string, unknown>
        for (const [k, v] of Object.entries(o as Record<string, unknown>)) if (!same(v, mine[k])) return {checked, failure: `${at()}: the service's ${k} is ${JSON.stringify(v)}, the rule's ${JSON.stringify(mine[k])}`}
      }
      checked++
    }
  }
  return {checked}
}

// A Schema's kind (the type side of Effect's Schema, 3.x or 4.x): a struct a record, string literals a choice, a
// tagged union of structs a variant on `_tag`, integers int (and nat where they are at least 0), Boolean bool, String a
// string, `X | null` and optional fields a maybe, a Schema.Class its fields. A number that isn't an integer, and every
// other Schema, is refused with the path to it.
export function fromSchema(schema: {ast: unknown, fields?: Record<string, {ast: unknown}>}): Kind<unknown> {
  const fail = (path: string, what: string): never => { throw new Error(`fromSchema: ${path || 'the schema'} is ${what}`) }
  type Ast = Mod
  const sym = (a: Ast, id: string) => { const k = Object.getOwnPropertySymbols(a.annotations ?? {}).find(x => x.description === id); return k ? a.annotations[k] : undefined }
  const num = (a: Ast, path: string): Kind<unknown> => {
    // v4: Number with checks; v3: a Refinement chain down to NumberKeyword.
    let int = false, min = -Infinity
    for (let x = a; x; x = x._tag === 'Refinement' ? x.from : undefined) {
      for (const c of x.checks ?? []) { const an = c.annotations ?? {}; if (an.representation?.id === 'effect/schema/isInt' || an.arbitraryConstraint?.number?.isInteger) int = true; if (typeof an.arbitraryConstraint?.minimum === 'number') min = Math.max(min, an.arbitraryConstraint.minimum) }
      const js = sym(x, 'effect/annotation/JSONSchema') as {type?: string, minimum?: number} | undefined, id = String(sym(x, 'effect/annotation/SchemaId')?.description ?? '')
      if (js?.type === 'integer' || id === 'effect/SchemaId/Int') int = true
      if (typeof js?.minimum === 'number') min = Math.max(min, js.minimum)
    }
    return int ? (min >= 0 ? dsl.nat : dsl.int) : fail(path, 'a number that may be fractional (an integer schema, Schema.Int, is read)')
  }
  const props = (a: Ast) => a.propertySignatures as {name: PropertyKey, type: Ast, isOptional?: boolean, context?: {isOptional?: boolean}}[]
  const go = (a: Ast, path: string): Kind<unknown> => {
    const tag = a?._tag as string
    if (tag === 'Transformation') return go(a.to, path)
    if (tag === 'Number' || tag === 'NumberKeyword' || (tag === 'Refinement' && /Number/.test(baseTag(a)))) return num(a, path)
    if (tag === 'Refinement') return go(a.from, path)
    if (tag === 'Boolean' || tag === 'BooleanKeyword') return dsl.bool
    if (tag === 'String' || tag === 'StringKeyword') return dsl.str()
    if (tag === 'Literal') return typeof a.literal === 'string' ? dsl.oneOf(a.literal) : fail(path, `the literal ${String(a.literal)} (string literals are read)`)
    if (tag === 'Union') {
      const types = a.types as Ast[], missing = types.filter(t => /^(Null|Undefined|UndefinedKeyword|Literal)$/.test(t._tag) && (t._tag !== 'Literal' || t.literal === null)), rest = types.filter(t => !missing.includes(t))
      if (missing.length && rest.length === 1) return dsl.maybe(go(rest[0]!, path))
      if (rest.every(t => t._tag === 'Literal' && typeof t.literal === 'string')) return dsl.oneOf(...rest.map(t => t.literal as string))
      const tagOf = (t: Ast) => { const p = (t._tag === 'Objects' || t._tag === 'TypeLiteral') ? props(t).find(x => x.name === '_tag') : undefined; return p?.type._tag === 'Literal' && typeof p.type.literal === 'string' ? p.type.literal as string : undefined }
      if (!missing.length && rest.every(tagOf)) return dsl.variant(Object.fromEntries(rest.map(t => [tagOf(t)!, fieldsOf(t, path, true)])) as never, {tag: '_tag'})
      return fail(path, 'a union other than of string literals, of structs tagged by _tag, or with null')
    }
    if (tag === 'Objects' || tag === 'TypeLiteral') { if (a.indexSignatures?.length) fail(path, 'a record with an index signature'); return dsl.record(fieldsOf(a, path, false) as never) }
    return fail(path, `a ${tag} schema (structs, literals, tagged unions, integers, booleans and strings are read)`)
  }
  const baseTag = (a: Ast): string => (a._tag === 'Refinement' ? baseTag(a.from) : a._tag)
  const fieldsOf = (a: Ast, path: string, tagged: boolean): Record<string, Kind<unknown>> => Object.fromEntries(props(a).filter(p => !(tagged && p.name === '_tag')).map(p => {
    const at = `${path ? `${path}.` : ''}${String(p.name)}`, k = go(p.type, at)
    return [String(p.name), (p.isOptional || p.context?.isOptional) && !(k instanceof Object && 'of' in k) ? dsl.maybe(k) : k]
  }))
  if (schema.fields && (schema.ast as Ast)?._tag !== 'Objects' && (schema.ast as Ast)?._tag !== 'TypeLiteral') return dsl.record(Object.fromEntries(Object.entries(schema.fields).map(([f, x]) => [f, go(x.ast as Ast, f)])) as never)
  return go(schema.ast as Ast, '')
}
