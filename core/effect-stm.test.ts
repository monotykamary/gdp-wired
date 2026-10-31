// Transactions on Effect 4.x (TxRef, Effect.tx, Effect.txRetry) and 3.x (TRef, STM.gen, STM.commit, STM.check,
// STM.retry), read by core/effect.ts: each transaction one atomic step, checked by running the service on Effect's
// runtime beside the rule (a waiting transaction interrupted, not left to commit later); a failure inside one rolled
// back; a method of several transactions read as every fiber's steps (core/system.ts's lift), a lost update refuted by
// a run of two fibers and seen on the runtime; the bank's laws proven on both lines; the CLI on a file using Schedule and
// STM; and what isn't read refused with why.
import {expect, test} from 'bun:test'
import * as effect from 'effect'
import {join} from 'node:path'
import {proveRule} from './dsl.ts'
import {extractEffect, fiberRun} from './effect.ts'
import {check} from './cli.ts'
import {inProject} from '../examples/effect-retry.ts'
import {bank3, bank4, bankLaws, raceSaves, readBank} from '../examples/effect-stm.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Any = any
const svc3 = (body: string) => `import {Data, Effect, STM, TRef} from 'effect'
export class No extends Data.TaggedError('No')<{}> {}
export const make = Effect.gen(function* () {
  const a = yield* TRef.make(5)
  const b = yield* TRef.make(0)
${body}
})`
const svc4 = (body: string) => `import {Effect, Schema, TxRef} from 'effect'
export class No extends Schema.TaggedError<No>()('No', {}) {}
export const make = Effect.gen(function* () {
  const a = yield* TxRef.make(5)
  const b = yield* TxRef.make(0)
${body}
})`

test('every TRef operation (3.x) and TxRef operation (4.x), in and out of transactions, runs as the rule says', () => {
  const ops3 = `  const move = Effect.fn('move')(function* (n: number) {
    yield* STM.gen(function* () {
      const x = yield* TRef.get(a)
      if (n < 0 || x < n) return yield* STM.fail(new No())
      yield* TRef.set(a, x - n)
      yield* TRef.update(b, y => y + n)
    })
  })
  const swap = () => STM.gen(function* () { const x = yield* TRef.getAndSet(a, 0); const y = yield* TRef.getAndUpdate(b, () => x); yield* TRef.set(a, y) }).pipe(STM.commit)
  const bump = (n: number) => STM.commit(STM.gen(function* () { const y = yield* TRef.updateAndGet(b, v => v + 1); return yield* TRef.modify(a, x => [y, x + (n > 0 ? 1 : 0)] as const) }))
  const peek = () => TRef.get(a)
  const reset = () => TRef.setAndGet(b, 0)
  return {move, swap, bump, peek, reset}`
  const ops4 = `  const move = Effect.fn('move')(function* (n: number) {
    yield* Effect.tx(Effect.gen(function* () {
      const x = yield* TxRef.get(a)
      if (n < 0 || x < n) return yield* new No()
      yield* TxRef.set(a, x - n)
      yield* TxRef.update(b, y => y + n)
    }))
  })
  const swap = () => Effect.tx(Effect.gen(function* () { const x = yield* TxRef.get(a); const y = yield* TxRef.modify(b, v => [v, x] as const); yield* TxRef.set(a, y) }))
  const bump = (n: number) => Effect.tx(Effect.gen(function* () { yield* TxRef.update(b, v => v + 1); return yield* TxRef.modify(a, x => [x, x + (n > 0 ? 1 : 0)] as const) }))
  const peek = () => TxRef.get(a)
  return {move, swap, bump, peek}`
  for (const [v, code] of [[3, svc3(ops3)], [4, svc4(ops4)]] as const) {
    const x = extractEffect(inProject(v, 'ops.ts', code), {entry: 'make'}) as Any
    expect([v, x.ok, x.refusals]).toEqual([v, true, []])
    expect(x.evidence.coverage.missed).toEqual([])
    expect(x.evidence.requests).toBeGreaterThan(1000)
  }
}, 300_000)

test('a transaction that waits (STM.check, STM.retry, Effect.txRetry) is a guard: refused until it can go, never committed later', () => {
  const wait3 = `  const take = (n: number) => STM.gen(function* () { const x = yield* TRef.get(a); yield* STM.check(() => n >= 0 && x >= n); yield* TRef.set(a, x - n) }).pipe(STM.commit)
  const takeOr = Effect.fn('takeOr')(function* (n: number) { yield* STM.gen(function* () { const x = yield* TRef.get(a); if (x < n) return yield* STM.retry; yield* TRef.set(a, x - n) }) })
  const give = (n: number) => TRef.update(a, x => x + Math.max(0, n))
  return {take, takeOr, give}`
  const wait4 = `  const take = Effect.fn('take')(function* (n: number) { yield* Effect.tx(Effect.gen(function* () { const x = yield* TxRef.get(a); if (n < 0 || x < n) return yield* Effect.txRetry; yield* TxRef.set(a, x - n) })) })
  const give = (n: number) => TxRef.update(a, x => x + Math.max(0, n))
  return {take, give}`
  for (const [v, code] of [[3, svc3(wait3)], [4, svc4(wait4)]] as const) {
    const x = extractEffect(inProject(v, 'wait.ts', code), {entry: 'make'}) as Any
    expect([v, x.ok, x.refusals]).toEqual([v, true, []])
    expect(x.evidence.refusedBoth).toBeGreaterThan(100)
    expect(x.notes.join('\n')).toMatch(/a transaction that waits .* is not taken until a TRef it read changes/)
    const r = x.rule
    expect(proveRule(r, [r.law('never below zero', ({a}: Any) => a.atLeast(0))])).toMatchObject({proven: true, checked: true})
  }
}, 300_000)

test('the bank (examples/effect-bank.ts, and in STM for 3.x): each method one transaction, its laws proven under any interleaving', () => {
  for (const v of [4, 3] as const) {
    const {x} = readBank(v), r = x.rule as Any
    expect([v, x.ok, x.refusals]).toEqual([v, true, []])
    for (const l of bankLaws(r)) expect([v, l.name, proveRule(r, [...x.invariants ?? [], l])]).toMatchObject([v, l.name, {proven: true, checked: true}])
  }
}, 300_000)

test('broken: save in two transactions is every fiber\'s two steps; a lost update refuted by two fibers, and seen on the runtime', async () => {
  for (const v of [4, 3] as const) {
    const {x, file} = readBank(v, 'two transactions'), r = x.rule as Any
    expect([v, x.ok, x.refusals]).toEqual([v, true, []])
    expect(r.machine.name).toBe('make, every fiber')
    expect(x.notes[0]).toMatch(/save is 2 steps .* the service's Refs \(checking, savings\) shared/)
    const verdict = proveRule(r, [...x.invariants ?? [], bankLaws(r)[0]!])
    expect(verdict.proven).toBe(false)
    const run = fiberRun(x, verdict.run!), fibers = new Set(verdict.run!.trace.map(q => q.fiber))
    expect(fibers.size).toBeGreaterThanOrEqual(2)
    expect(run.filter(s => /its step 1 of 2/.test(s)).length).toBeGreaterThanOrEqual(2)
    // (the same two saves at once on Effect's runtime: both read before either writes)
    const raced = await raceSaves(v, file)
    expect(raced.checking + raced.savings).toBe(110)
  }
}, 300_000)

test('fibers on a service of plain Refs: off by default (each method one step), on when asked: a get-then-set loses an update', () => {
  const code = `import {Effect, Ref} from 'effect'
export const make = Effect.gen(function* () {
  const n = yield* Ref.make(0)
  const total = yield* Ref.make(0)
  const add = Effect.fn('add')(function* (k: number) {
    const x = yield* Ref.get(n)
    yield* Ref.set(n, x + Math.max(0, k))
    yield* Ref.update(total, t => t + Math.max(0, k))
  })
  return {add}
})`
  const one = extractEffect(code, {file: 'svc.ts', entry: 'make', effect}), r1 = one.rule as Any
  expect([one.ok, r1.machine.name]).toEqual([true, 'make'])
  expect(proveRule(r1, [r1.law('n counts every add', ({n, total}: Any) => n.eq(total))])).toMatchObject({proven: true, checked: true})
  const many = extractEffect(code, {file: 'svc.ts', entry: 'make', effect, fibers: true}), r = many.rule as Any
  expect([many.ok, r.machine.name]).toEqual([true, 'make, every fiber'])
  const v = proveRule(r, [r.law('n counts every add', ({n, total}: Any) => n.eq(total))])
  expect(v.proven).toBe(false)
  expect(fiberRun(many, v.run!).filter(s => /add\(k = [1-9]/.test(s)).length).toBeGreaterThanOrEqual(1)
}, 120_000)

test('what a method carries from one step to the next is what the code has there, a let assigned again included', () => {
  // (one fiber at a time, its steps back to back, is the method as written: each conforms on the runtime)
  const code = svc4(`  const go = Effect.fn('go')(function* (k: number) {
    let x = yield* TxRef.get(a)
    x = x + Math.max(0, k)
    yield* Effect.tx(TxRef.set(b, x))
    x = x + 1
    yield* Effect.tx(TxRef.update(a, y => y + x - x))
    return yield* Effect.tx(TxRef.modify(b, y => [x, y] as const))
  })
  return {go}`)
  const x = extractEffect(inProject(4, 'let.ts', code), {entry: 'make'}) as Any
  expect([x.ok, x.refusals, x.rule.machine.name]).toEqual([true, [], 'make, every fiber'])
  expect(x.source).toMatch(/let x = yield\* __gdp_Ref.get\(__gdp_go_x\)/)
  expect(x.source.match(/yield\* __gdp_Ref.set\(__gdp_go_x, x\)/g).length).toBe(3)
  // (a return of nothing in a later step ends the call too: the fiber goes back to where it starts (a review's go(skip)))
  const skip = extractEffect(inProject(4, 'skip.ts', svc4(`  const go = Effect.fn('go')(function* (skip: boolean) {
    yield* TxRef.update(a, n => n + 1)
    if (skip) return yield* Effect.void
    yield* TxRef.set(b, 1)
  })
  return {go}`)), {entry: 'make'}) as Any, r = skip.rule
  expect([skip.ok, r.machine.name]).toEqual([true, 'make, every fiber'])
  expect(skip.source).toContain('if (skip) { (yield* Effect.void); yield* __gdp_Ref.set(__gdp_pc, 0); return }')
  const g = r.compiled(), ps = r.encodeParams({})
  let st = g.init(ps)
  for (const q of [{skip: 1}, {skip: 1}, {skip: 0}, {skip: 0}]) st = g.step(ps, st, r.encodeInput({method: 'go', go_skip: q.skip, fiber: 0}))
  expect(r.decode(st)).toMatchObject({a: 7, b: 1})
}, 120_000)

test('a Ref of the service\'s is shared among the fibers whatever its name (a review\'s __gate): the waiting fiber sees it open', () => {
  const code = svc4(`  const __gate = yield* TxRef.make(0)
  const bad = yield* TxRef.make(0)
  const open = Effect.fn('open')(function* () { yield* TxRef.set(__gate, 1); yield* TxRef.get(__gate) })
  const act = Effect.fn('act')(function* () {
    const x = yield* TxRef.get(__gate)
    yield* Effect.tx(Effect.gen(function* () { const g = yield* TxRef.get(__gate); if (x !== 0 || g !== 1) return yield* Effect.txRetry; yield* TxRef.set(bad, 1) }))
  })
  return {open, act}`)
  const x = extractEffect(inProject(4, 'gate.ts', code), {entry: 'make'}), r = x.rule as Any
  expect([x.ok, r.machine.name, '__gate' in r.machine.state, 'bad' in r.machine.state]).toEqual([true, 'make, every fiber', true, true])
  const v = proveRule(r, [...x.invariants ?? [], r.law('nothing bad', ({bad}: Any) => bad.eq(0))])
  expect(v.proven).toBe(false)
  expect(fiberRun(x, v.run!).join('; ')).toMatch(/act.*open.*act, its step 2 of 2/)
}, 120_000)

test('what the transaction reader doesn\'t take is refused where it is, with the reason', () => {
  const cases: [3 | 4, string, RegExp][] = [
    [4, `  const go = Effect.fn('go')(function* (n: number) { yield* TxRef.set(a, n); yield* Effect.tx(Effect.gen(function* () { const x = yield* TxRef.get(b); if (x > 3) return yield* new No(); yield* TxRef.set(b, x + 1) })) })\n  return {go}`, /a transaction that fails in a step after the first/],
    [4, `  const go = Effect.fn('go')(function* (n: number) { yield* Effect.tx(Effect.gen(function* () { yield* TxRef.set(a, n) })); if (n > 3) return yield* new No() })\n  return {go}`, /fails after writing a/],
    [3, `  const go = (n: number) => STM.gen(function* () { yield* STM.check(n > 0) }).pipe(STM.commit)\n  return {go}`, /STM.check of other than \(\) => condition/],
    [3, `  const go = (n: number) => STM.commit(STM.flatMap(TRef.get(a), x => TRef.set(b, x + n)))\n  return {go}`, /STM.flatMap \(of STM: gen, commit/],
    [4, `  const go = Effect.fn('go')(function* () { return yield* Effect.txRetry })\n  return {go}`, /Effect.txRetry outside a transaction/],
    [4, `  const go = Effect.fn('go')(function* () { const {x} = {x: yield* TxRef.get(a)}; yield* Effect.tx(TxRef.set(b, x)) })\n  return {go}`, /a name is carried, not a pattern/],
    // (several effects on the state where a step can't be cut: in one branch, in an Effect.gen, in an arrow)
    [4, `  const go = Effect.fn('go')(function* () { if (true) { const x = yield* TxRef.get(a); yield* Effect.yieldNow; yield* TxRef.set(a, x + 1); yield* TxRef.update(b, t => t + 1) } })\n  return {go}`, /runs 3 effects on the state one after another in one statement, and another fiber's step may come between them/],
    [4, `  const go = Effect.fn('go')(function* () { yield* Effect.gen(function* () { const x = yield* TxRef.get(a); yield* TxRef.set(a, x + 1) }) })\n  return {go}`, /runs 2 effects on the state one after another in one statement/],
    [3, `  const go = () => Effect.gen(function* () { const x = yield* TRef.get(a); yield* TRef.set(b, x) })\n  return {go}`, /runs 2 effects on the state one after another, and another fiber's step may come between them: write the method as Effect.fn/],
    [4, `  const go = Effect.fn('go')(function* () { yield* TxRef.set(a, yield* TxRef.get(b)); yield* TxRef.set(b, 1) })\n  return {go}`, /runs 2 effects on the state one after another in one statement/],
    [4, `  const __gdp_gate = yield* TxRef.make(0)\n  const go = Effect.fn('go')(function* () { const x = yield* TxRef.get(a); yield* Effect.tx(TxRef.set(__gdp_gate, x)) })\n  return {go}`, /a name of the code starts with __gdp_/],
  ]
  for (const [v, body, why] of cases) {
    const x = extractEffect(inProject(v, 'bad.ts', v === 3 ? svc3(body) : svc4(body)), {entry: 'make'})
    expect([body, x.ok]).toEqual([body, false])
    expect(x.refusals[0]!.what).toMatch(why)
  }
}, 300_000)

test('the CLI on a file using Schedule and STM (4.x, examples/effect-bank.ts; 3.x in a project of its own): laws as comments', async () => {
  const {rules, exit} = await check([join(import.meta.dir, '../examples/effect-bank.ts')], {ms: 8000, propose: false})
  expect(exit).toBe(0)
  expect(rules.map(r => [r.entry, r.laws.map(l => `${l.name}: ${l.verdict}`)])).toEqual([
    ['backoff', ['the delay never exceeds the cap: proven', 'never more than 5 retries: proven', 'it stops after the deadline: proven']],
    ['make', ['the money is conserved: proven', 'checking is never overdrawn: proven']],
  ])
  // 3.x: the same bank in STM with its backoff, and the bank broken (save in two transactions): broken, with its run.
  const laws = '// gdp: law the money is conserved: checking + savings == 100\n'
  const ok3 = inProject(3, 'bank.ts', `${bank3().replace('export const make', `// gdp: law the delay never exceeds the cap: delay <= 2000\nexport const backoff = Schedule.exponential('100 millis').pipe(Schedule.union(Schedule.spaced('2 seconds')), Schedule.intersect(Schedule.recurs(5)))\n${laws}export const make`).replace("import {Data, Effect, STM, TRef} from 'effect'", "import {Data, Effect, STM, Schedule, TRef} from 'effect'")}`)
  const r3 = await check([ok3], {ms: 8000, propose: false})
  expect(r3.exit).toBe(0)
  expect(r3.rules.flatMap(r => r.laws.map(l => `${r.entry}: ${l.name}: ${l.verdict}`))).toEqual(['backoff: the delay never exceeds the cap: proven', 'make: the money is conserved: proven'])
  for (const [v, code] of [[4, bank4('two transactions')], [3, bank3('two transactions')]] as const) {
    // (the 4.x bank file states the law above its make already)
    const file = inProject(v, 'broken.ts', v === 4 ? code : code.replace('export const make', `${laws}export const make`))
    const b = await check([file], {ms: 8000, propose: false}), law = b.rules.find(r => r.entry === 'make')!.laws.find(l => l.name === 'the money is conserved')!
    expect([v, b.exit, law.verdict]).toEqual([v, 1, 'broken'])
    expect(law.run!.length).toBeGreaterThanOrEqual(4)
  }
}, 300_000)
