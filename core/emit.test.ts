// End-to-end verification for core/emit.ts and core/emit-cli.ts:
//   - crossCheck: dynamically import emitted TypeScript modules and compare against interpreter() and compiled()
//   - determinism: byte-for-byte & digest parity in-process and across fresh subprocesses
//   - hygiene: zero import / require / Function / eval tokens anywhere in emitted source
//   - CLI: --out, --check (pass, 1-char edit diff -> exit 1, missing -> exit 1), unproven -> exit 2
//   - closed-loop --verify: TS reader re-proves emitted laws and refutes deliberate mutants (exit 1)
import {afterAll, describe, expect, test} from 'bun:test'
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {
  GDP_WIRED_VERSION,
  Unproven,
  bool,
  chart,
  count,
  forall,
  fun,
  int,
  maybe,
  min,
  nat,
  oneOf,
  recur,
  relation,
  rule,
  str,
  upTo,
  when,
} from './dsl.ts'
import {seeded} from './machine.ts'
import {sha256Hex} from './emit.ts'
import {emitMain, verifyEmittedFile} from './emit-cli.ts'
import {interpretQ, loadQJs, qparse, qshow} from './rationals.ts'
import {approve, approveLaws, accounts, accountLaws, accountSteps, hold, holdLaws, holdSteps, jobs, jobLaws, jobSteps, seats, seatLaws, seatSteps} from '../examples/datatypes.ts'
import {minutes, minuteLaws, larger, largerLaws, room, roomLaws} from '../examples/functions.ts'
import {feeSplit, feeLaws, limiter, limiterLaws, ledger, ledgerLaws} from '../examples/rationals.ts'
import {defaultReviewParams, makeReviewRouting, makeReviewRoutingLaws, reviewRouting, reviewRoutingLaws} from '../examples/review-routing.ts'

const root = join(import.meta.dir, '..')
const tmp = mkdtempSync(join(tmpdir(), 'gdp-wired-emit-test-'))
let seq = 0

afterAll(() => {
  rmSync(tmp, {recursive: true, force: true})
})

const HYGIENE_RE = /\b(import|require|Function|eval)\b/

async function loadEmitted<T = Record<string, unknown>>(name: string, source: string): Promise<{file: string, mod: T}> {
  expect(source).not.toMatch(HYGIENE_RE)
  const file = join(tmp, `${++seq}-${name}.ts`)
  writeFileSync(file, source)
  const mod = await import(pathToFileURL(file).href) as T
  return {file, mod}
}

function runCli(args: string[]): {status: number, stdout: string, stderr: string} {
  const r = spawnSync(process.execPath, [join(root, 'core/cli.ts'), ...args], {
    cwd: root,
    encoding: 'utf8',
    timeout: 60_000,
  })
  return {status: r.status ?? 2, stdout: r.stdout ?? '', stderr: r.stderr ?? ''}
}

// --- Version & SHA-256 parity ----------------------------------------------------------------------------------------

describe('emit metadata and digest primitives', () => {
  test('GDP_WIRED_VERSION matches package.json and pure-JS sha256 matches node:crypto', () => {
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8')) as {version: string}
    expect(GDP_WIRED_VERSION).toBe(pkg.version)
    for (const sample of ['', 'abc', 'hello world', 'a'.repeat(55), 'a'.repeat(56), 'a'.repeat(64), 'gdp-wired emit λ 0.61.0']) {
      const want = createHash('sha256').update(sample, 'utf8').digest('hex')
      expect(sha256Hex(sample)).toBe(want)
    }
  })

  test('unproven rules and empty law lists throw Unproven by default', () => {
    const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
      .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
    const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
    const uncapped = budget.step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))
    expect(() => uncapped.emit({laws: [bounded]})).toThrow(Unproven)

    const noLaws = rule('empty').inputs({x: nat}).state({s: 0}).step(({x, s}) => ({s: s.plus(x)}))
    expect(() => noLaws.emit()).toThrow(Unproven)

    const brokenReview = makeReviewRouting('drop-tamper')
    expect(() => brokenReview.emit({laws: makeReviewRoutingLaws(brokenReview)})).toThrow(Unproven)

    const badRat = feeSplit('payout 97.6%')
    expect(() => badRat.emit({laws: feeLaws(badRat)})).toThrow(Unproven)
  })
})

// --- Cross-check emitted modules against interpreter() & compiled() --------------------------------------------------

describe('emit crossCheck across Rule, Fun, RatRule, and Chart', () => {
  test('README budget: crossCheck vs interpreter() and compiled() + --verify', async () => {
    const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
      .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
    const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
    const res = budget.emit({laws: [bounded]})
    expect(res.allProven).toBe(true)
    expect(res.verify.verifiable).toBe(true)
    const {file, mod} = await loadEmitted<{
      init: (p: {b: number, m: number}) => {s: number}
      step: (p: {b: number, m: number}, st: {s: number}, i: {c: number}) => {s: number}
    }>('budget', res.source)

    const interp = budget.interpreter(), comp = budget.compiled(), rand = seeded(11)
    for (let trial = 0; trial < 40; trial++) {
      const p = {b: rand(20), m: rand(12)}
      const ps = budget.encodeParams(p)
      let stI = interp.init(ps), stC = comp.init(ps), stE = mod.init(p)
      expect(stE.s).toBe(budget.decode(stI).s as number)
      for (let k = 0; k < 15; k++) {
        const inp = {c: rand(25)}
        const enc = budget.encodeInput(inp)
        stI = interp.step(ps, stI, enc)
        stC = comp.step(ps, stC, enc)
        stE = mod.step(p, stE, inp)
        expect(stE.s).toBe(budget.decode(stI).s as number)
        expect(stE.s).toBe(budget.decode(stC).s as number)
      }
    }
    const ver = await verifyEmittedFile(file, res)
    expect(ver).toMatchObject({ok: true, exit: 0, proven: 1, broken: 0})
  })

  test('caps (maps + bool + flags + state/step laws): crossCheck + --verify', async () => {
    const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
      .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
      .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
    const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
    const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
    const once = caps.stepLaw('a grant adds one to its day', ({day, Day}, after) => after.Day.at(day).eq(Day.at(day).plus(1)), ({granted}) => granted)
    const res = caps.emit({laws: [dayCap], stepLaws: [onlyUp, once]})
    expect(res.allProven).toBe(true)
    expect(res.verify.verifiable).toBe(true)

    const {file, mod} = await loadEmitted<{
      init: (p: {d: number}) => {Acct: Map<number, number>, Day: Map<number, number>}
      step: (p: {d: number}, st: {Acct: Map<number, number>, Day: Map<number, number>}, i: {acct: number, day: number, ok: boolean}) => {Acct: Map<number, number>, Day: Map<number, number>}
    }>('caps', res.source)

    const interp = caps.interpreter(), comp = caps.compiled(), rand = seeded(23)
    for (let trial = 0; trial < 25; trial++) {
      const p = {d: rand(5)}, ps = caps.encodeParams(p)
      let stI = interp.init(ps), stC = comp.init(ps), stE = mod.init(p)
      for (let k = 0; k < 20; k++) {
        const inp = {acct: rand(6), day: rand(4), ok: rand(2) === 1}
        const enc = caps.encodeInput(inp)
        stI = interp.step(ps, stI, enc)
        stC = comp.step(ps, stC, enc)
        stE = mod.step(p, stE, inp)
        for (let key = 0; key < 6; key++) {
          expect(stE.Acct.get(key) ?? 0).toBe(stI.maps.Acct?.get(key) ?? 0)
          expect(stE.Acct.get(key) ?? 0).toBe(stC.maps.Acct?.get(key) ?? 0)
          expect(stE.Day.get(key) ?? 0).toBe(stI.maps.Day?.get(key) ?? 0)
          expect(stE.Day.get(key) ?? 0).toBe(stC.maps.Day?.get(key) ?? 0)
        }
      }
    }
    const ver = await verifyEmittedFile(file, res)
    expect(ver).toMatchObject({ok: true, exit: 0, proven: 3, broken: 0})
  })

  test('accounts (record map + oneOf): crossCheck + --verify', async () => {
    const r = accounts()
    const res = r.emit({laws: accountLaws(r), stepLaws: accountSteps(r)})
    expect(res.allProven).toBe(true)
    expect(res.verify.verifiable).toBe(true)
    const {file, mod} = await loadEmitted<{
      init: () => {Acct: Map<number, {limit: number, spent: number, frozen: boolean}>}
      step: (p: Record<string, never>, st: {Acct: Map<number, {limit: number, spent: number, frozen: boolean}>}, i: {op: 'limit' | 'spend' | 'freeze', who: number, amount: number}) => {Acct: Map<number, {limit: number, spent: number, frozen: boolean}>}
    }>('accounts', res.source)

    const interp = r.interpreter(), comp = r.compiled(), rand = seeded(31)
    const ops = ['limit', 'spend', 'freeze'] as const
    let stI = interp.init({}), stC = comp.init({}), stE = mod.init()
    for (let k = 0; k < 40; k++) {
      const inp = {op: ops[rand(3)]!, who: rand(4), amount: rand(20)}
      const enc = r.encodeInput(inp)
      stI = interp.step({}, stI, enc)
      stC = comp.step({}, stC, enc)
      stE = mod.step({}, stE, inp)
      const dI = r.decode(stI).Acct as Record<string, {limit: number, spent: number, frozen: boolean}>
      const dC = r.decode(stC).Acct as Record<string, {limit: number, spent: number, frozen: boolean}>
      for (let who = 0; who < 4; who++) {
        const cellE = stE.Acct.get(who) ?? {limit: 0, spent: 0, frozen: false}
        const cellI = dI[String(who)] ?? {limit: 0, spent: 0, frozen: false}
        const cellC = dC[String(who)] ?? {limit: 0, spent: 0, frozen: false}
        expect(cellE).toEqual(cellI)
        expect(cellE).toEqual(cellC)
      }
    }
    const ver = await verifyEmittedFile(file, res)
    expect(ver).toMatchObject({ok: true, exit: 0, proven: 2, broken: 0})
  })

  test('minutes (divBy + assume): crossCheck + --verify', async () => {
    const r = minutes()
    const res = r.emit({laws: minuteLaws(r)})
    expect(res.allProven).toBe(true)
    expect(res.verify.verifiable).toBe(true)
    const {file, mod} = await loadEmitted<{
      init: (p: {cap: number}) => {minute: number, count: number, last: number}
      step: (p: {cap: number}, st: {minute: number, count: number, last: number}, i: {t: number}) => {minute: number, count: number, last: number}
    }>('minutes', res.source)

    const interp = r.interpreter(), comp = r.compiled(), rand = seeded(41)
    const p = {cap: 3}, ps = r.encodeParams(p)
    let stI = interp.init(ps), stC = comp.init(ps), stE = mod.init(p), t = 0
    for (let k = 0; k < 40; k++) {
      t += rand(45)
      const inp = {t}, enc = r.encodeInput(inp)
      stI = interp.step(ps, stI, enc)
      stC = comp.step(ps, stC, enc)
      stE = mod.step(p, stE, inp)
      expect(stE).toEqual(r.decode(stI) as typeof stE)
      expect(stE).toEqual(r.decode(stC) as typeof stE)
    }
    const ver = await verifyEmittedFile(file, res)
    expect(ver).toMatchObject({ok: true, exit: 0, proven: 2, broken: 0})
  })

  test('hold (variant state), seats (variant map), jobs (items list), larger & room & retry (fns/recur), window (history), kinds (int/maybe/str/upTo)', async () => {
    // hold
    {
      const r = hold()
      const res = r.emit({laws: holdLaws(r), stepLaws: holdSteps(r)})
      expect(res.allProven).toBe(true)
      const {mod} = await loadEmitted<{init: (p: {cap: number, wait: number}) => Record<string, unknown>, step: (p: {cap: number, wait: number}, s: Record<string, unknown>, i: Record<string, unknown>) => Record<string, unknown>}>('hold', res.source)
      const interp = r.interpreter(), comp = r.compiled(), rand = seeded(51)
      const p = {cap: 50, wait: 10}, ps = r.encodeParams(p), ops = ['hold', 'release', 'refund'] as const
      let stI = interp.init(ps), stC = comp.init(ps), stE = mod.init(p), now = 0
      for (let k = 0; k < 40; k++) {
        now += rand(8)
        const inp = {op: ops[rand(3)]!, amount: rand(60), now}, enc = r.encodeInput(inp)
        stI = interp.step(ps, stI, enc); stC = comp.step(ps, stC, enc); stE = mod.step(p, stE, inp)
        expect(stE).toEqual(r.decode(stI))
        expect(stE).toEqual(r.decode(stC))
      }
    }
    // seats
    {
      const r = seats()
      const res = r.emit({laws: seatLaws(r), stepLaws: seatSteps(r)})
      expect(res.allProven).toBe(true)
      const {mod} = await loadEmitted<{init: () => {Seats: Map<number, unknown>}, step: (p: Record<string, never>, s: {Seats: Map<number, unknown>}, i: Record<string, unknown>) => {Seats: Map<number, unknown>}}>('seats', res.source)
      const interp = r.interpreter(), rand = seeded(53), ops = ['hold', 'buy'] as const
      let stI = interp.init({}), stE = mod.init(), now = 0
      for (let k = 0; k < 30; k++) {
        now += rand(7)
        const inp = {op: ops[rand(2)]!, seat: rand(4), who: rand(3), now}, enc = r.encodeInput(inp)
        stI = interp.step({}, stI, enc); stE = mod.step({}, stE, inp)
        const dI = r.decode(stI).Seats as Record<string, unknown>
        for (let s = 0; s < 4; s++) expect(stE.Seats.get(s) ?? {tag: 'free'}).toEqual(dI[String(s)] ?? {tag: 'free'})
      }
    }
    // jobs
    {
      const r = jobs()
      const res = r.emit({laws: jobLaws(r), stepLaws: jobSteps(r)})
      expect(res.allProven).toBe(true)
      const {mod} = await loadEmitted<{init: (p: {cap: number}) => {Queue: unknown[]}, step: (p: {cap: number}, s: {Queue: unknown[]}, i: Record<string, unknown>) => {Queue: unknown[]}}>('jobs', res.source)
      const interp = r.interpreter(), rand = seeded(57), p = {cap: 4}, ps = r.encodeParams(p), ops = ['push', 'pop'] as const
      let stI = interp.init(ps), stE = mod.init(p)
      for (let k = 0; k < 30; k++) {
        const inp = {op: ops[rand(2)]!, job: {id: rand(100), prio: rand(10)}}, enc = r.encodeInput(inp)
        stI = interp.step(ps, stI, enc); stE = mod.step(p, stE, inp)
        expect(stE.Queue).toEqual(r.decode(stI).Queue as unknown[])
      }
    }
    // retry (recur)
    {
      const delay = recur('delay', {zero: 1, next: (_, d) => min(d.times(2), 64)}, {'at least 1': (_, d) => d.atLeast(1), 'at most 64': (_, d) => d.atMost(64)})
      const retry = rule('retry').inputs({failed: bool, now: nat}).state({tries: 0, next: 0, last: 0}).fns({delay})
        .assume(({now, last}) => now.atLeast(last))
        .step(({failed, now, tries, next, delay: d}) => ({tries: when(failed, tries.plus(1), 0), next: when(failed.and(now.atLeast(next)), now.plus(d(tries)), next), last: now}))
      const soon = retry.law('next try at most 64 after last', ({next, last}) => next.atMost(last.plus(64)))
      const res = retry.emit({laws: [soon]})
      expect(res.allProven).toBe(true)
      const {mod} = await loadEmitted<{init: () => Record<string, number>, step: (p: Record<string, never>, s: Record<string, number>, i: {failed: boolean, now: number}) => Record<string, number>}>('retry', res.source)
      const interp = retry.interpreter(), rand = seeded(61)
      let stI = interp.init({}), stE = mod.init(), now = 0
      for (let k = 0; k < 30; k++) {
        now += rand(20)
        const inp = {failed: rand(3) !== 0, now}
        stI = interp.step({}, stI, retry.encodeInput(inp))
        stE = mod.step({}, stE, inp)
        expect(stE).toEqual(retry.decode(stI) as Record<string, number>)
      }
    }
    // larger & room (custom fns)
    {
      const resL = larger.emit({laws: largerLaws})
      const {mod: modL} = await loadEmitted<{init: () => {high: number, seen: number}, step: (p: Record<string, never>, s: {high: number, seen: number}, i: {a: number}) => {high: number, seen: number}}>('larger', resL.source)
      const compL = larger.compiled()
      let sI = compL.init({}), sE = modL.init()
      for (const a of [0, 5, 2, 11, 3]) {
        sI = compL.step({}, sI, larger.encodeInput({a}))
        sE = modL.step({}, sE, {a})
        expect(sE).toEqual(larger.decode(sI) as typeof sE)
      }
      const rRoom = room(), resR = rRoom.emit({laws: roomLaws(rRoom)})
      const {mod: modR} = await loadEmitted<{init: () => {people: number, shakes: number}, step: (p: Record<string, never>, s: {people: number, shakes: number}, i: Record<string, never>) => {people: number, shakes: number}}>('room', resR.source)
      const compR = rRoom.compiled()
      let rI = compR.init({}), rE = modR.init()
      for (let k = 0; k < 8; k++) {
        rI = compR.step({}, rI, {}); rE = modR.step({}, rE, {})
        expect(rE).toEqual(rRoom.decode(rI) as typeof rE)
      }
    }
    // window (history + sums + queries + prune)
    {
      const win = rule('window limit').params({w: nat, c: nat, now: nat}).inputs({forced: bool, t: nat}).log('forced', 't')
        .sums({ours: (rec, {now, w}) => count(rec.forced.not().and(rec.t.atMost(now), now.lt(rec.t.plus(w))))})
        .queries({seen: (rec, {t, w}) => count(t.lt(rec.t.plus(w)))})
        .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
        .keep(({forced, admitted}) => forced.or(admitted))
        .relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
        .prune('t', ({w}) => w)
      const ceil = win.law('window ceiling', ({ours, c}) => ours.atMost(c))
      const res = win.emit({laws: [ceil]})
      expect(res.allProven).toBe(true)
      const {mod} = await loadEmitted<{init: (p: {w: number, c: number, now: number}) => {ours: number}, step: (p: {w: number, c: number, now: number}, s: {ours: number}, i: {forced: boolean, t: number}) => {ours: number}}>('window', res.source)
      const p = {w: 10, c: 2, now: 15}, ps = win.encodeParams(p), interp = win.interpreter(), rand = seeded(67)
      let stI = interp.init(ps), stE = mod.init(p), t = 0
      for (let k = 0; k < 25; k++) {
        t += rand(4)
        const inp = {forced: rand(4) === 0, t}
        stI = interp.step(ps, stI, win.encodeInput(inp))
        stE = mod.step(p, stE, inp)
        expect(stE.ours).toBe(win.decode(stI).ours as number)
      }
    }
    // kinds: int, maybe, str({like}), upTo
    {
      const r = rule('kinded').params({floor: int}).inputs({delta: int, pct: upTo(100), tag: str({like: ['prod:*']}), opt: maybe(nat)})
        .state({bal: int.from(0), label: str({like: ['prod:*']}).from(''), saved: maybe(nat).from(null)})
        .pre(({floor}) => floor.atMost(0))
        .step(({floor, delta, pct, tag, opt, bal, label, saved}) => ({
          bal: when(bal.plus(delta).atLeast(floor), bal.plus(delta), bal),
          label: when(tag.like('prod:*').and(pct.atLeast(50)), tag, label),
          saved: when(opt.isSome, opt, saved),
        }))
      const stayAbove = r.law('balance stays at or above floor', ({bal, floor}) => bal.atLeast(floor))
      const res = r.emit({laws: [stayAbove]})
      expect(res.allProven).toBe(true)
      const {mod} = await loadEmitted<{
        init: (p: {floor: number}) => {bal: number, label: string, saved: number | null}
        step: (p: {floor: number}, s: {bal: number, label: string, saved: number | null}, i: {delta: number, pct: number, tag: string, opt: number | null}) => {bal: number, label: string, saved: number | null}
      }>('kinded', res.source)
      const p = {floor: -10}, ps = r.encodeParams(p), interp = r.interpreter(), rand = seeded(71)
      const tags = ['', 'prod:a', 'dev:b', 'prod:zz']
      let stI = interp.init(ps), stE = mod.init(p)
      for (let k = 0; k < 30; k++) {
        const inp = {delta: rand(15) - 7, pct: rand(101), tag: tags[rand(4)]!, opt: rand(3) === 0 ? null : rand(20)}
        stI = interp.step(ps, stI, r.encodeInput(inp))
        stE = mod.step(p, stE, inp)
        expect(stE).toEqual(r.decode(stI) as typeof stE)
      }
    }
  })

  test('canEdit (pure Fun) & approve (variant+record Fun): exhaustive and randomized crossCheck + --verify', async () => {
    const canEdit = fun('can edit')
      .inputs({role: oneOf('viewer', 'editor', 'admin'), isOwner: bool, locked: bool})
      .returns(({role, isOwner, locked}) => ({
        ok: role.is('admin').or(locked.not().and(role.is('editor').or(isOwner))),
      }))
    const laws = [
      canEdit.law('admins can always edit', ({role}) => role.is('admin'), out => out.ok),
      canEdit.law('locked blocks non-admins', ({role, locked}) => [locked, role.is('admin').not()], out => out.ok.not()),
    ]
    const res = canEdit.emit({laws})
    expect(res.allProven).toBe(true)
    expect(res.verify.verifiable).toBe(true)
    const {file, mod} = await loadEmitted<{canEdit: (args: {role: 'viewer' | 'editor' | 'admin', isOwner: boolean, locked: boolean}) => {ok: boolean}}>('canEdit', res.source)
    const comp = canEdit.compiled()
    for (const role of ['viewer', 'editor', 'admin'] as const) {
      for (const isOwner of [false, true]) {
        for (const locked of [false, true]) {
          const inp = {role, isOwner, locked}
          expect(mod.canEdit(inp)).toEqual(canEdit.run(inp))
          expect(mod.canEdit(inp)).toEqual(comp(inp))
        }
      }
    }
    const ver = await verifyEmittedFile(file, res)
    expect(ver).toMatchObject({ok: true, exit: 0, proven: 2, broken: 0})

    // approve (variant + record Fun)
    const app = approve()
    const resA = app.emit({laws: approveLaws(app)})
    expect(resA.allProven).toBe(true)
    const {mod: modA} = await loadEmitted<{approveAPayment: (args: Record<string, unknown>) => {ok: boolean, charged: number}}>('approve', resA.source)
    const compA = app.compiled(), rand = seeded(79)
    for (let k = 0; k < 60; k++) {
      const which = rand(3)
      const pay = which === 0
        ? {tag: 'card', amount: rand(900), last4: rand(10000), verified: rand(2) === 1}
        : which === 1
          ? {tag: 'cash', amount: rand(350)}
          : {tag: 'voucher', cover: rand(101)}
      const who = {tier: rand(2) === 0 ? 'basic' : 'gold', limit: rand(500), blocked: rand(4) === 0}
      const inp = {pay, who}
      expect(modA.approveAPayment(inp)).toEqual(app.run(inp))
      expect(modA.approveAPayment(inp)).toEqual(compA(inp))
    }
  })

  test('examples/review-routing.generated.ts: crossCheck vs run()/compiled(), --check, and --verify', async () => {
    const genPath = join(root, 'examples/review-routing.generated.ts')
    const genSource = readFileSync(genPath, 'utf8')
    expect(genSource).not.toMatch(HYGIENE_RE)
    const genMod = await import(pathToFileURL(genPath).href) as {
      reviewRouting: (args: Record<string, unknown>, params?: Record<string, unknown>) => {decision: string, final: string}
      defaultParams: () => Record<string, number>
    }
    expect(genMod.defaultParams()).toEqual({...defaultReviewParams})
    const comp = reviewRouting.compiled(), rand = seeded(83)
    const verdicts = ['approve', 'reject', 'review'] as const
    const edges = [0, 0.1499, 0.15, 0.1501, 0.3499, 0.35, 0.3501, 0.4499, 0.45, 0.4501, 0.5499, 0.55, 0.5501, 0.7499, 0.75, 0.7501, 1]
    for (let k = 0; k < 150; k++) {
      const pick = () => (rand(3) === 0 ? edges[rand(edges.length)]! : rand(10001) / 10000)
      const inp = {
        relevance: pick(),
        risk: pick(),
        ageConcern: pick(),
        tamperSuspected: rand(4) === 0,
        explicitRequest: rand(3) === 0,
        secondOpinion: verdicts[rand(3)]!,
      }
      expect(genMod.reviewRouting(inp)).toEqual(reviewRouting.run(inp, defaultReviewParams))
      expect(genMod.reviewRouting(inp)).toEqual(comp(inp, defaultReviewParams))
    }
    const res = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    expect(res.source).toBe(genSource)
    const ver = await verifyEmittedFile(genPath, res)
    expect(ver).toMatchObject({ok: true, exit: 0, proven: 5, broken: 0})
  })

  test('RatRule (feeSplit, limiter, ledger): exact BigInt rational crossCheck vs interpretQ & loadQJs', async () => {
    for (const [label, r, laws, paramsRaw, reqsRaw] of [
      ['feeSplit', feeSplit(), feeLaws(), {}, [{payment: '0.1'}, {payment: '1/3'}, {payment: '12.50'}, {payment: '999999.99'}]],
      ['limiter', limiter(), limiterLaws(), {cap: '2'}, [{cost: '0.5'}, {cost: '1/3'}, {cost: '0.4'}, {cost: '0'}]],
      ['ledger', ledger(), ledgerLaws(), {}, [{op: '0', amount: '10/3'}, {op: '2', amount: '1/3'}, {op: '1', amount: '0.5'}, {op: '2', amount: '2.5'}]],
    ] as const) {
      const res = r.emit({laws: [...laws]})
      expect(res.allProven).toBe(true)
      expect(res.verify.verifiable).toBe(false)
      expect(res.verify.reasons[0]).toContain('RatRule')
      const {mod} = await loadEmitted<{
        toRat: (x: unknown) => readonly [bigint, bigint]
        formatRat: (x: readonly [bigint, bigint]) => string
        init: (p: Record<string, readonly [bigint, bigint]>) => Record<string, readonly [bigint, bigint]>
        allowed: (p: Record<string, readonly [bigint, bigint]>, s: Record<string, readonly [bigint, bigint]>, i: Record<string, readonly [bigint, bigint]>) => boolean
        step: (p: Record<string, readonly [bigint, bigint]>, s: Record<string, readonly [bigint, bigint]>, i: Record<string, readonly [bigint, bigint]>) => Record<string, readonly [bigint, bigint]>
      }>(label, res.source)
      const qI = interpretQ(r.machine), qC = loadQJs(r.machine)
      const pQ = Object.fromEntries(Object.entries(paramsRaw).map(([k, v]) => [k, qparse(v)]))
      const pE = Object.fromEntries(Object.entries(paramsRaw).map(([k, v]) => [k, mod.toRat(v)]))
      let sI = qI.init(pQ), sC = qC.init(pQ), sE = mod.init(pE)
      for (const req of reqsRaw) {
        const iQ = Object.fromEntries(Object.entries(req).map(([k, v]) => [k, qparse(v)]))
        const iE = Object.fromEntries(Object.entries(req).map(([k, v]) => [k, mod.toRat(v)]))
        expect(mod.allowed(pE, sE, iE)).toBe(qI.allowed(pQ, sI, iQ))
        sI = qI.step(pQ, sI, iQ); sC = qC.step(pQ, sC, iQ); sE = mod.step(pE, sE, iE)
        for (const k of Object.keys(sI)) {
          expect(mod.formatRat(sE[k]!)).toBe(qshow(sI[k]!))
          expect(mod.formatRat(sE[k]!)).toBe(qshow(sC[k]!))
        }
      }
    }
  })

  test('Chart (nested states + history, and flat verifiable chart): crossCheck + --verify', async () => {
    const order = chart('order').context({retries: 0}).states({
      new: {}, active: {states: {paid: {}, shipped: {}}, history: true}, refunded: {final: true}, delivered: {final: true},
    })
      .on('pay', {from: 'new', to: 'active'})
      .on('ship', {from: 'active.paid', to: 'active.shipped'})
      .on('refund', {from: 'active.paid', to: 'refunded'})
      .on('deliver', {from: 'active.shipped', to: 'delivered'})
    const deliveredFinal = order.stepLaw('delivered stays delivered', (b, a) => b.in('delivered').implies(a.in('delivered')))
    const res = order.emit({stepLaws: [deliveredFinal]})
    expect(res.allProven).toBe(true)
    const {mod} = await loadEmitted<{
      init: () => Record<string, unknown>
      step: (p: Record<string, never>, s: Record<string, unknown>, i: {event: string}) => Record<string, unknown>
    }>('orderChart', res.source)
    const r = order.rule, interp = r.interpreter(), comp = r.compiled()
    let sI = interp.init({}), sC = comp.init({}), sE = mod.init()
    for (const event of ['pay', 'ship', 'deliver', 'refund', 'pay']) {
      const enc = r.encodeInput({event})
      sI = interp.step({}, sI, enc); sC = comp.step({}, sC, enc); sE = mod.step({}, sE, {event})
      expect(sE).toEqual(r.decode(sI))
      expect(sE).toEqual(r.decode(sC))
    }

    // Flat statechart without dotted compound history fields is directly verifiable by TS reader!
    const door = chart('door').states({closed: {}, open: {}, locked: {final: true}})
      .on('open', {from: 'closed', to: 'open'})
      .on('close', {from: 'open', to: 'closed'})
      .on('lock', {from: 'closed', to: 'locked'})
    const lockFinal = door.stepLaw('locked is final', (b, a) => b.in('locked').implies(a.in('locked')))
    const resDoor = door.emit({stepLaws: [lockFinal]})
    expect(resDoor.allProven).toBe(true)
    expect(resDoor.verify.verifiable).toBe(true)
    const {file: doorFile} = await loadEmitted('doorChart', resDoor.source)
    const verDoor = await verifyEmittedFile(doorFile, resDoor)
    expect(verDoor).toMatchObject({ok: true, exit: 0, proven: 1, broken: 0})
  })
})

// --- Determinism & CLI (--out, --check, --verify, mutant refutation) -------------------------------------------------

describe('emit determinism, CLI, and mutant refutation', () => {
  test('byte-identical output and digest in-process and across two separate subprocesses', () => {
    const a = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    const b = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    expect(a.source).toBe(b.source)
    expect(a.digest).toBe(b.digest)

    const p1 = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle'])
    const p2 = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle'])
    expect(p1.status).toBe(0)
    expect(p2.status).toBe(0)
    expect(p1.stdout).toBe(p2.stdout)
    expect(p1.stdout).toBe(a.source)
  })

  test('CLI --out, --check (pass, 1-char edit diff -> exit 1, missing -> exit 1), --verify, and unproven -> exit 2', async () => {
    const outFile = join(tmp, 'cli-review.generated.ts')
    // Missing file under --check -> exit 1
    expect(runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle', '--out', outFile, '--check']).status).toBe(1)

    // Write + verify -> exit 0
    const writeRun = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle', '--out', outFile, '--verify'])
    expect(writeRun.status).toBe(0)
    expect(writeRun.stdout).toContain('verified 5/5 laws')

    // --check + --verify -> exit 0
    const checkOk = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle', '--out', outFile, '--check', '--verify'])
    expect(checkOk.status).toBe(0)

    // 1-char edit -> --check exits 1 with short diff
    const original = readFileSync(outFile, 'utf8')
    writeFileSync(outFile, original.replace('0.55', '0.56'))
    const checkDrift = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle', '--out', outFile, '--check'])
    expect(checkDrift.status).toBe(1)
    expect(checkDrift.stderr).toContain('out of date')
    expect(checkDrift.stderr).toContain('0.56')
    expect(checkDrift.stderr).toContain('0.55')

    // Unproven module export -> exit 2 (never writes)
    const badMod = join(tmp, 'bad-rule.ts')
    writeFileSync(badMod, `
      import {rule, nat, min, when} from ${JSON.stringify(join(root, 'core/dsl.ts'))}
      const b = rule('uncapped').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0}).step(({b, c, s}) => ({s: when(s.lt(b), s.plus(c), s)}))
      export const badLaw = b.law('bounded', ({s, b, m}) => s.atMost(b.plus(m)))
      export const uncapped = b
      void min
    `)
    const badOut = join(tmp, 'should-not-exist.ts')
    const unprovenRun = runCli(['emit', `${badMod}#uncapped`, '--out', badOut])
    expect(unprovenRun.status).toBe(2)
    expect(() => readFileSync(badOut, 'utf8')).toThrow()

    // Non-verifiable target (RatRule) with --verify -> honest exit 2
    const ratMod = join(tmp, 'rat-export.ts')
    writeFileSync(ratMod, `
      import {feeSplit, feeLaws} from ${JSON.stringify(join(root, 'examples/rationals.ts'))}
      const r = feeSplit()
      export const bundle = {ratRule: r, laws: feeLaws(r)}
    `)
    const ratVerify = await emitMain([`${ratMod}#bundle`, '--out', join(tmp, 'rat-out.ts'), '--verify'])
    expect(ratVerify).toBe(2)
  })

  test('--verify refutes deliberate mutants in emitted decision and stateful code (exit 1)', async () => {
    // Mutants on emitted reviewRouting
    const reviewRes = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    const reviewMutants: [string, string, string][] = [
      ['drop tamper guard', 'args.tamperSuspected ? "reject" :', 'false ? "reject" :'],
      ['flip clearRisk comparison', 'args.risk < params.clearRisk', 'args.risk <= params.clearRisk'],
      ['break escalation reject->approve', 'decision === "review"', 'decision === "review" || decision === "reject"'],
    ]
    for (const [label, from, to] of reviewMutants) {
      const splitAt = reviewRes.source.indexOf('export function reviewRoutingScaled')
      expect(splitAt).toBeGreaterThan(0)
      const head = reviewRes.source.slice(0, splitAt)
      const body = reviewRes.source.slice(splitAt)
      expect(body).toContain(from)
      const mutated = head + body.replaceAll(from, to)
      const mutFile = join(tmp, `mut-review-${++seq}.ts`)
      writeFileSync(mutFile, mutated)
      const ver = await verifyEmittedFile(mutFile, reviewRes)
      expect({label, ok: ver.ok, exit: ver.exit, broken: ver.broken}).toMatchObject({label, ok: false, exit: 1})
      expect(ver.broken).toBeGreaterThan(0)
    }

    // Mutant on emitted README budget (drop Math.min cap)
    const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
      .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
    const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
    const budgetRes = budget.emit({laws: [bounded]})
    const mutBudgetFile = join(tmp, `mut-budget-${++seq}.ts`)
    writeFileSync(mutBudgetFile, budgetRes.source.replace('Math.min(input.c, params.m)', 'input.c'))
    const verB = await verifyEmittedFile(mutBudgetFile, budgetRes)
    expect(verB).toMatchObject({ok: false, exit: 1, broken: 1})

    // Mutant on emitted caps (flip `< params.d` to `<= params.d`)
    const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
      .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
      .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
    const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
    const capsRes = caps.emit({laws: [dayCap]})
    const mutCapsFile = join(tmp, `mut-caps-${++seq}.ts`)
    writeFileSync(mutCapsFile, capsRes.source.replace('< params.d', '<= params.d'))
    const verC = await verifyEmittedFile(mutCapsFile, capsRes)
    expect(verC).toMatchObject({ok: false, exit: 1, broken: 1})
  })
})
