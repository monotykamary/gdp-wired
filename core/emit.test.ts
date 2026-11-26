// End-to-end verification for core/emit.ts and core/emit-cli.ts:
//   - crossCheck: dynamically import emitted TypeScript modules and compare against interpreter() and compiled()
//   - determinism: byte-for-byte & digest parity in-process and across fresh subprocesses
//   - hygiene: zero import / require / Function / eval tokens anywhere in emitted source
//   - CLI: --out, --check (pass, 1-char edit diff -> exit 1, missing -> exit 1), unproven -> exit 2
//   - differential --verify: exhaustive small domains + randomized + error/throw parity across Rule, Fun, RatRule, Chart,
//     plus emitter mutant refutation (exit 1)
import {afterAll, describe, expect, test} from 'bun:test'
import {createHash} from 'node:crypto'
import {spawnSync} from 'node:child_process'
import {existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {pathToFileURL} from 'node:url'
import {
  GDP_WIRED_VERSION,
  Unproven,
  bool,
  chart,
  count,
  decimal,
  everyKey,
  fixedInt,
  fold,
  forall,
  fun,
  int,
  loop,
  max,
  maybe,
  min,
  nat,
  no,
  oneOf,
  record,
  recur,
  relation,
  rule,
  sizedSort,
  someKey,
  str,
  upTo,
  variant,
  when,
  yes,
} from './dsl.ts'
import {DEC_ROUND_HELPER_LINES, scaleDecimalHalfEven} from './decimal-round.ts'
import {compileJs, seeded} from './machine.ts'
import {C_OPS, E_OPS, MACHINE_PARTS, QC_OPS, QE_OPS} from './codegen.ts'
import {KIND_NAMES, emitFold, emitLoop, emitRatRule, emitRule, sha256Hex} from './emit.ts'
import {sha256Hex as sharedSha256Hex} from './sha256.ts'
import {emitMain, verifyEmittedFile} from './emit-cli.ts'
import {interpretQ, loadQJs, nonneg, rat, ratRule, rmax, rmin, rwhen} from './rationals.ts'
import {qparse, qshow} from './q.ts'
import {approve, approveLaws, accounts, accountLaws, accountSteps, hold, holdLaws, holdSteps, jobs, jobLaws, jobSteps, seats, seatLaws, seatSteps} from '../examples/datatypes.ts'
import {minutes, minuteLaws, larger, largerLaws, room, roomLaws} from '../examples/functions.ts'
import {feeSplit, feeLaws, limiter, limiterLaws, ledger, ledgerLaws} from '../examples/rationals.ts'
import {defaultReviewParams, makeReviewRouting, makeReviewRoutingLaws, reviewRouting, reviewRoutingLaws} from '../examples/review-routing.ts'
import {scope as scopeList, scopeLaws} from '../examples/lists.ts'
import {searchTree, searchTreeLaws, sheet, sheetLaws} from '../examples/trees.ts'
import {invoices, invoiceLaws, metered, meteredLaws} from '../examples/invoices.ts'
import {book as orderBook, bookLaws} from '../examples/orderbook.ts'
import {rollup, rollupLaws, signoffs, signoffLaws, orgChart, orgChartLaws} from '../examples/folds.ts'
import {pagesNonEmpty, retryCapped, sweepOnce} from '../examples/nonterm.ts'
import {ledger as existsLedger, ledgerLaws as existsLedgerLaws} from '../examples/exists.ts'
import {patterns as scopePatterns, grants as scopeGrants} from '../examples/scopes.ts'

const root = join(import.meta.dir, '..')
const tmp = mkdtempSync(join(tmpdir(), 'gdp-wired-emit-test-'))
let seq = 0

afterAll(() => {
  rmSync(tmp, {recursive: true, force: true})
})

const HYGIENE_RE = /\b(import|require|Function|eval)\b/

async function loadEmitted<T = Record<string, unknown>>(name: string, source: string): Promise<{file: string, mod: T}> {
  expect(source).not.toMatch(HYGIENE_RE)
  expect(source).not.toContain('// gdp: law')
  const file = join(tmp, `${++seq}-${name}.ts`)
  writeFileSync(file, source)
  const mod = await import(pathToFileURL(file).href) as T
  return {file, mod}
}

function runCli(args: string[], cwd: string = root): {status: number, stdout: string, stderr: string} {
  const r = spawnSync(process.execPath, [join(root, 'core/cli.ts'), ...args], {
    cwd,
    encoding: 'utf8',
    timeout: 60_000,
  })
  return {status: r.status ?? 2, stdout: r.stdout ?? '', stderr: r.stderr ?? ''}
}

// --- Version & SHA-256 parity ----------------------------------------------------------------------------------------

describe('emit metadata and digest primitives', () => {
  test('GDP_WIRED_VERSION matches package.json and pure-JS sha256 matches node:crypto', () => {
    expect(sha256Hex).toBe(sharedSha256Hex)
    const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8')) as {version: string}
    expect(GDP_WIRED_VERSION).toBe(pkg.version)
    for (const sample of ['', 'abc', 'hello world', 'a'.repeat(55), 'a'.repeat(56), 'a'.repeat(64), 'gdp-wired emit λ 0.61.0']) {
      const want = createHash('sha256').update(sample, 'utf8').digest('hex')
      expect(sha256Hex(sample)).toBe(want)
    }
    // compileJs refusal contract preserved through shared core/codegen.ts printer
    const tupEachMachine = rule('tup-each').sorts('N').relations({M: ['N', 'N']})
      .step(({M}) => ({M: M.each((x, y) => M.has(x, y))})).machine
    expect(() => compileJs(tupEachMachine)).toThrow('compileJs takes no tuple key at every key')
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

// --- Cross-check emitted modules against interpreter() & compiled() + differential --verify --------------------------

describe('emit crossCheck across Rule, Fun, RatRule, and Chart', () => {
  test('README budget: crossCheck vs interpreter() and compiled() + differential --verify', async () => {
    const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
      .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
    const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
    const res = budget.emit({laws: [bounded]})
    expect(res.allProven).toBe(true)
    expect(res.source).not.toContain('export class ')
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
    const ver = await verifyEmittedFile(file, {kind: 'rule', rule: budget}, res)
    expect(ver).toMatchObject({ok: true, exit: 0})
    expect(ver.checked).toBeGreaterThan(200)
  })

  test('caps (maps + bool + flags + state/step laws): crossCheck + differential --verify', async () => {
    const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
      .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
      .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
    const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
    const onlyUp = caps.stepLaw('no count goes down', ({Day}, after) => forall(k => Day.at(k).atMost(after.Day.at(k))))
    const once = caps.stepLaw('a grant adds one to its day', ({day, Day}, after) => after.Day.at(day).eq(Day.at(day).plus(1)), ({granted}) => granted)
    const res = caps.emit({laws: [dayCap], stepLaws: [onlyUp, once]})
    expect(res.allProven).toBe(true)

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
    const ver = await verifyEmittedFile(file, {kind: 'rule', rule: caps}, res)
    expect(ver).toMatchObject({ok: true, exit: 0})
    expect(ver.checked).toBeGreaterThan(200)
  })

  test('accounts (record map + oneOf): crossCheck + differential --verify', async () => {
    const r = accounts()
    const res = r.emit({laws: accountLaws(r), stepLaws: accountSteps(r)})
    expect(res.allProven).toBe(true)
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
    const ver = await verifyEmittedFile(file, {kind: 'rule', rule: r}, res)
    expect(ver).toMatchObject({ok: true, exit: 0})
  })

  test('minutes (divBy + assume): crossCheck + differential --verify', async () => {
    const r = minutes()
    const res = r.emit({laws: minuteLaws(r)})
    expect(res.allProven).toBe(true)
    const {file, mod} = await loadEmitted<{
      init: (p: {cap: number}) => {minute: number, count: number, last: number}
      step: (p: {cap: number}, st: {minute: number, count: number, last: number}, i: {t: number}) => {minute: number, count: number, last: number}
    }>('minutes', res.source)

    const interp = r.interpreter(), comp = r.compiled(), rand = seeded(41)
    const p = {cap: 3}, ps = r.encodeParams(p as never)
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
    const ver = await verifyEmittedFile(file, {kind: 'rule', rule: r}, res)
    expect(ver).toMatchObject({ok: true, exit: 0})
  })

  test('hold (variant state), seats (variant map), jobs (items list), larger & room & retry (fns/recur), window (history), kinds (int/maybe/str/upTo)', async () => {
    // hold
    {
      const r = hold()
      const res = r.emit({laws: holdLaws(r), stepLaws: holdSteps(r)})
      expect(res.allProven).toBe(true)
      const {file, mod} = await loadEmitted<{init: (p: {cap: number, wait: number}) => Record<string, unknown>, step: (p: {cap: number, wait: number}, s: Record<string, unknown>, i: Record<string, unknown>) => Record<string, unknown>}>('hold', res.source)
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
      expect((await verifyEmittedFile(file, {kind: 'rule', rule: r}, res)).ok).toBe(true)
    }
    // seats
    {
      const r = seats()
      const res = r.emit({laws: seatLaws(r), stepLaws: seatSteps(r)})
      expect(res.allProven).toBe(true)
      const {file, mod} = await loadEmitted<{init: () => {Seats: Map<number, unknown>}, step: (p: Record<string, never>, s: {Seats: Map<number, unknown>}, i: Record<string, unknown>) => {Seats: Map<number, unknown>}}>('seats', res.source)
      const interp = r.interpreter(), rand = seeded(53), ops = ['hold', 'buy'] as const
      let stI = interp.init({}), stE = mod.init(), now = 0
      for (let k = 0; k < 30; k++) {
        now += rand(7)
        const inp = {op: ops[rand(2)]!, seat: rand(4), who: rand(3), now}, enc = r.encodeInput(inp)
        stI = interp.step({}, stI, enc); stE = mod.step({}, stE, inp)
        const dI = r.decode(stI).Seats as Record<string, unknown>
        for (let s = 0; s < 4; s++) expect(stE.Seats.get(s) ?? {tag: 'free'}).toEqual(dI[String(s)] ?? {tag: 'free'})
      }
      expect((await verifyEmittedFile(file, {kind: 'rule', rule: r}, res)).ok).toBe(true)
    }
    // jobs
    {
      const r = jobs()
      const res = r.emit({laws: jobLaws(r), stepLaws: jobSteps(r)})
      expect(res.allProven).toBe(true)
      const {file, mod} = await loadEmitted<{init: (p: {cap: number}) => {Queue: unknown[]}, step: (p: {cap: number}, s: {Queue: unknown[]}, i: Record<string, unknown>) => {Queue: unknown[]}}>('jobs', res.source)
      const interp = r.interpreter(), rand = seeded(57), p = {cap: 4}, ps = r.encodeParams(p), ops = ['push', 'pop'] as const
      let stI = interp.init(ps), stE = mod.init(p)
      for (let k = 0; k < 30; k++) {
        const inp = {op: ops[rand(2)]!, job: {id: rand(100), prio: rand(10)}}, enc = r.encodeInput(inp)
        stI = interp.step(ps, stI, enc); stE = mod.step(p, stE, inp)
        expect(stE.Queue).toEqual(r.decode(stI).Queue as unknown[])
      }
      expect((await verifyEmittedFile(file, {kind: 'rule', rule: r}, res)).ok).toBe(true)
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
      const {file, mod} = await loadEmitted<{init: () => Record<string, number>, step: (p: Record<string, never>, s: Record<string, number>, i: {failed: boolean, now: number}) => Record<string, number>}>('retry', res.source)
      const interp = retry.interpreter(), rand = seeded(61)
      let stI = interp.init({}), stE = mod.init(), now = 0
      for (let k = 0; k < 30; k++) {
        now += rand(20)
        const inp = {failed: rand(3) !== 0, now}
        stI = interp.step({}, stI, retry.encodeInput(inp))
        stE = mod.step({}, stE, inp)
        expect(stE).toEqual(retry.decode(stI) as Record<string, number>)
      }
      expect((await verifyEmittedFile(file, {kind: 'rule', rule: retry}, res)).ok).toBe(true)
    }
    // larger & room (custom fns)
    {
      const resL = larger.emit({laws: largerLaws})
      const {file: fileL, mod: modL} = await loadEmitted<{init: () => {high: number, seen: number}, step: (p: Record<string, never>, s: {high: number, seen: number}, i: {a: number}) => {high: number, seen: number}}>('larger', resL.source)
      const compL = larger.compiled()
      let sI = compL.init({}), sE = modL.init()
      for (const a of [0, 5, 2, 11, 3]) {
        sI = compL.step({}, sI, larger.encodeInput({a}))
        sE = modL.step({}, sE, {a})
        expect(sE).toEqual(larger.decode(sI) as typeof sE)
      }
      expect((await verifyEmittedFile(fileL, {kind: 'rule', rule: larger}, resL)).ok).toBe(true)

      const rRoom = room(), resR = rRoom.emit({laws: roomLaws(rRoom)})
      const {file: fileR, mod: modR} = await loadEmitted<{init: () => {people: number, shakes: number}, step: (p: Record<string, never>, s: {people: number, shakes: number}, i: Record<string, never>) => {people: number, shakes: number}}>('room', resR.source)
      const compR = rRoom.compiled()
      let rI = compR.init({}), rE = modR.init()
      for (let k = 0; k < 8; k++) {
        rI = compR.step({}, rI, {}); rE = modR.step({}, rE, {})
        expect(rE).toEqual(rRoom.decode(rI) as typeof rE)
      }
      expect((await verifyEmittedFile(fileR, {kind: 'rule', rule: rRoom}, resR)).ok).toBe(true)
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
      const {file, mod} = await loadEmitted<{init: (p: {w: number, c: number, now: number}) => {ours: number}, step: (p: {w: number, c: number, now: number}, s: {ours: number}, i: {forced: boolean, t: number}) => {ours: number}}>('window', res.source)
      const p = {w: 10, c: 2, now: 15}, ps = win.encodeParams(p), interp = win.interpreter(), rand = seeded(67)
      let stI = interp.init(ps), stE = mod.init(p), t = 0
      for (let k = 0; k < 25; k++) {
        t += rand(4)
        const inp = {forced: rand(4) === 0, t}
        stI = interp.step(ps, stI, win.encodeInput(inp))
        stE = mod.step(p, stE, inp)
        expect(stE.ours).toBe(win.decode(stI).ours as number)
      }
      expect((await verifyEmittedFile(file, {kind: 'rule', rule: win}, res)).ok).toBe(true)
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
      const {file, mod} = await loadEmitted<{
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
      expect((await verifyEmittedFile(file, {kind: 'rule', rule: r}, res)).ok).toBe(true)
    }
  })

  test('canEdit (pure Fun) & approve (variant+record Fun): exhaustive and randomized crossCheck + differential --verify', async () => {
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
    const ver = await verifyEmittedFile(file, {kind: 'fun', fun: canEdit}, res)
    expect(ver).toMatchObject({ok: true, exit: 0, exhaustive: true, checked: 12})

    // approve (variant + record Fun)
    const app = approve()
    const resA = app.emit({laws: approveLaws(app)})
    expect(resA.allProven).toBe(true)
    const {file: fileA, mod: modA} = await loadEmitted<{approveAPayment: (args: Record<string, unknown>) => {ok: boolean, charged: number}}>('approve', resA.source)
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
    const verA = await verifyEmittedFile(fileA, {kind: 'fun', fun: app}, resA)
    expect(verA).toMatchObject({ok: true, exit: 0})
  })

  test('decimal(places, {round: "half-even"}): exact digit rounding, negatives, exponents, strict default unchanged, and shared implementation', async () => {
    // 1. Strict default decimal(4) still throws past 4 places
    const strictDec = decimal(4)
    expect(() => strictDec.encode('x', 0.73219)).toThrow(RangeError)
    expect(() => strictDec.encode('x', 0.00005)).toThrow(RangeError)
    expect(() => strictDec.encode('x', 1e-7)).toThrow(RangeError)
    expect(() => strictDec.encode('x', 1e-5)).toThrow(RangeError)

    // 2. Half-even digit rounding on exact halves, more places, negatives, and exponent forms
    const cases: [number | string, number][] = [
      [0, 0],
      [-0, 0],
      [0.00005, 0],
      [0.00015, 2],
      [0.00025, 2],
      [0.00035, 4],
      [0.00045, 4],
      [0.000051, 1],
      [0.73219, 7322],
      [0.73214, 7321],
      [0.99995, 10000],
      [0.99996, 10000],
      [1.00005, 10000],
      [1.00015, 10002],
      [-0.00005, 0],
      [-0.00015, -2],
      [-0.00025, -2],
      [-0.00035, -4],
      [-0.73219, -7322],
      [1e-7, 0],
      [5e-7, 0],
      [5e-5, 0],
      [1.5e-4, 2],
      [2.5e-4, 2],
      [-1.5e-4, -2],
      [-2.5e-4, -2],
      [1.23e-2, 123],
      ['1e-7', 0],
      ['5e-5', 0],
      ['1.5e-4', 2],
      ['2.5e-4', 2],
      ['-0.00015', -2],
    ]
    const roundedDec = decimal(4, {round: 'half-even'})
    for (const [input, scaled] of cases) {
      expect(scaleDecimalHalfEven(input, 4, 'x')).toBe(scaled)
      expect(Object.is(scaleDecimalHalfEven(input, 4, 'x'), -0)).toBe(false)
      const enc = roundedDec.encode('x', input)
      expect((enc.x ?? 0) - (enc['x$neg'] ?? 0)).toBe(scaled)
    }
    expect(() => scaleDecimalHalfEven(Number.NaN, 4, 'x')).toThrow(RangeError)
    expect(() => scaleDecimalHalfEven(Number.POSITIVE_INFINITY, 4, 'x')).toThrow(RangeError)

    // 3. Shared implementation invariant: DEC_ROUND_HELPER_LINES body matches scaleDecimalHalfEven core logic
    const helperText = DEC_ROUND_HELPER_LINES.join('\n')
    expect(helperText).toContain('const shift = exp - fracPart.length + places')
    expect(helperText).toContain("const odd = '13579'.includes(wholeStr[wholeStr.length - 1]!)")
    expect(helperText).toContain("const up = firstDrop > '5' || (firstDrop === '5' && (hasMore || odd))")

    // 4. Round-trip Fun with decimal(4, {round: 'half-even'}) + exact halves + differential --verify + mutant refutation
    const echo = fun('echo rounded')
      .inputs({x: decimal(4, {round: 'half-even'})})
      .returns(({x}) => ({y: x, nonneg: x.atLeast(0)}))
    const echoLaw = echo.law('nonneg matches y >= 0', ({x}) => x.atLeast(0), out => out.nonneg)
    const res = echo.emit({laws: [echoLaw]})
    expect(res.allProven).toBe(true)
    expect(res.source).toContain('inputs rounded half-even to 10^-4; laws hold for the rounded values')
    const {file, mod} = await loadEmitted<{echoRounded: (a: {x: number}) => {y: number, nonneg: boolean}}>('echoRounded', res.source)
    for (const [raw, scaled] of cases) {
      if (typeof raw !== 'number') continue
      const got = mod.echoRounded({x: raw})
      const want = echo.run({x: raw})
      expect(got).toEqual(want)
      expect(got.y).toBe(scaled / 10000)
    }
    const ver = await verifyEmittedFile(file, {kind: 'fun', fun: echo}, res)
    expect(ver).toMatchObject({ok: true, exit: 0})

    // Mutant: change half-even tie-break `(hasMore || odd)` to half-up `true` -> differential --verify MUST exit 1!
    expect(res.source).toContain('(hasMore || odd)')
    const mutFile = join(tmp, `mut-round-${++seq}.ts`)
    writeFileSync(mutFile, res.source.replace('(hasMore || odd)', 'true'))
    const mutVer = await verifyEmittedFile(mutFile, {kind: 'fun', fun: echo}, res)
    expect(mutVer).toMatchObject({ok: false, exit: 1})
    expect(mutVer.mismatch).toBeTruthy()
  })

  test('examples/review-routing.generated.ts: clean CSE output, half-even rounding parity, repo-root header, crossCheck, and differential --verify', async () => {
    const genPath = join(root, 'examples/review-routing.generated.ts')
    const genSource = readFileSync(genPath, 'utf8')
    expect(genSource).not.toMatch(HYGIENE_RE)
    expect(genSource).not.toContain('// gdp: law')
    expect(genSource).toContain('// Generated by gdp-wired 0.61.0 from examples/review-routing.ts#reviewRoutingBundle. Do not edit.')
    expect(genSource).toContain('// To change behavior, edit the model and its laws, then run from the repository root: npx gdp-wired-cli emit examples/review-routing.ts#reviewRoutingBundle --out examples/review-routing.generated.ts')
    expect(genSource).toContain('inputs rounded half-even to 10^-4; laws hold for the rounded values')
    // Shared subterm `decision` is bound once and reused in `final` (no duplicated decision tree).
    expect(genSource).toContain('const decision:')
    expect(genSource).toContain('const final:')

    const genMod = await import(pathToFileURL(genPath).href) as {
      reviewRouting: (args: Record<string, unknown>, params?: Record<string, unknown>) => {decision: string, final: string}
      defaultParams: () => Record<string, number>
    }
    expect(genMod.defaultParams()).toEqual({...defaultReviewParams})
    const comp = reviewRouting.compiled(), rand = seeded(83)
    const verdicts = ['approve', 'reject', 'review'] as const
    const edges = [0, 0.00005, 0.00015, 0.00025, 1e-7, 5e-5, 1.5e-4, 0.14995, 0.15, 0.15005, 0.34995, 0.35, 0.35005, 0.44995, 0.45, 0.45005, 0.54995, 0.55, 0.55005, 0.73219, 0.74995, 0.75, 0.75005, 0.99995, 1]
    for (let k = 0; k < 150; k++) {
      const pick = () => (rand(2) === 0 ? edges[rand(edges.length)]! : rand(1_000_001) / 1_000_000)
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

    // Raw model probabilities (>4 decimal places, exact halves, exponents) round half-even identically in emitted and interpreter.
    for (const rel of [0.73219, 0.00005, 0.00015, 0.00025, 1e-7, 5e-5, 1.5e-4, 0.55005]) {
      const inp = {relevance: rel, risk: 0.12345, ageConcern: 1e-7, tamperSuspected: false, explicitRequest: false, secondOpinion: 'review' as const}
      expect(genMod.reviewRouting(inp)).toEqual(reviewRouting.run(inp, defaultReviewParams))
    }
    // Strict decimal(4) threshold params still reject >4 decimal places identically in emitted and interpreter.
    const badParam = {...defaultReviewParams, approveAt: 0.55123}
    const baseInp = {relevance: 0.72, risk: 0.12, ageConcern: 0.05, tamperSuspected: false, explicitRequest: false, secondOpinion: 'review' as const}
    expect(() => reviewRouting.run(baseInp, badParam)).toThrow(RangeError)
    expect(() => genMod.reviewRouting(baseInp, badParam)).toThrow(RangeError)

    const res = reviewRouting.emit({
      laws: reviewRoutingLaws,
      defaultParams: defaultReviewParams,
      name: 'reviewRouting',
      provenance: {model: 'examples/review-routing.ts#reviewRoutingBundle', out: 'examples/review-routing.generated.ts'},
    })
    expect(res.source).toBe(genSource)
    const ver = await verifyEmittedFile(genPath, {kind: 'fun', fun: reviewRouting, defaultParams: defaultReviewParams}, res)
    expect(ver).toMatchObject({ok: true, exit: 0})
    expect(ver.checked).toBeGreaterThan(1000)
    expect(ver.throwsMatched).toBeGreaterThan(0)
  })

  test('RatRule (feeSplit, limiter, ledger): exact BigInt rational crossCheck vs interpretQ & loadQJs + differential --verify', async () => {
    for (const [label, r, laws, paramsRaw, reqsRaw] of [
      ['feeSplit', feeSplit(), feeLaws(), {}, [{payment: '0.1'}, {payment: '1/3'}, {payment: '12.50'}, {payment: '999999.99'}]],
      ['limiter', limiter(), limiterLaws(), {cap: '2'}, [{cost: '0.5'}, {cost: '1/3'}, {cost: '0.4'}, {cost: '0'}]],
      ['ledger', ledger(), ledgerLaws(), {}, [{op: '0', amount: '10/3'}, {op: '2', amount: '1/3'}, {op: '1', amount: '0.5'}, {op: '2', amount: '2.5'}]],
    ] as const) {
      const res = r.emit({laws: [...laws]})
      expect(res.allProven).toBe(true)
      const {file, mod} = await loadEmitted<{
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
      const ver = await verifyEmittedFile(file, {kind: 'ratRule', ratRule: r}, res)
      expect(ver).toMatchObject({ok: true, exit: 0})
      expect(ver.checked).toBeGreaterThan(200)
    }
  })

  test('Chart (nested states + history, and flat chart): crossCheck + differential --verify', async () => {
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
    const {file, mod} = await loadEmitted<{
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
    const verOrder = await verifyEmittedFile(file, {kind: 'chart', chart: order}, res)
    expect(verOrder).toMatchObject({ok: true, exit: 0})

    const door = chart('door').states({closed: {}, open: {}, locked: {final: true}})
      .on('open', {from: 'closed', to: 'open'})
      .on('close', {from: 'open', to: 'closed'})
      .on('lock', {from: 'closed', to: 'locked'})
    const lockFinal = door.stepLaw('locked is final', (b, a) => b.in('locked').implies(a.in('locked')))
    const resDoor = door.emit({stepLaws: [lockFinal]})
    expect(resDoor.allProven).toBe(true)
    const {file: doorFile} = await loadEmitted('doorChart', resDoor.source)
    const verDoor = await verifyEmittedFile(doorFile, {kind: 'chart', chart: door}, resDoor)
    expect(verDoor).toMatchObject({ok: true, exit: 0})
  })
})

// --- Determinism, CLI (--out, --check, --verify), and Emitter Mutant Refutation --------------------------------------

describe('emit determinism, CLI, and emitter mutant refutation', () => {
  test('byte-identical output and digest in-process, across subprocesses, and from repo root vs subdirectory', () => {
    const a = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    const b = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    expect(a.source).toBe(b.source)
    expect(a.digest).toBe(b.digest)

    const p1 = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle'])
    const p2 = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle'])
    expect(p1.status).toBe(0)
    expect(p2.status).toBe(0)
    expect(p1.stdout).toBe(p2.stdout)
    expect(p1.stdout).toContain('// Generated by gdp-wired 0.61.0 from examples/review-routing.ts#reviewRoutingBundle. Do not edit.')

    // Repo-root-relative header: emit from repo root vs subdirectory produces byte-identical output,
    // and --check from a subdirectory passes (tested in an isolated git repo so it holds even in .git-stripped CI trees).
    const fakeRepo = join(tmp, 'fake-git-repo')
    const subDir = join(fakeRepo, 'models')
    mkdirSync(join(fakeRepo, '.git'), {recursive: true})
    mkdirSync(subDir, {recursive: true})
    writeFileSync(join(subDir, 'gate.ts'), `
      import {fun, bool} from ${JSON.stringify(join(root, 'core/dsl.ts'))}
      export const gate = fun('gate').inputs({ok: bool}).returns(({ok}) => ({allow: ok}))
      export const gateLaws = [gate.law('ok allows', ({ok}) => ok, out => out.allow)]
      export const gateBundle = {fun: gate, laws: gateLaws, name: 'gate'}
    `)
    const fromRoot = runCli(['emit', 'models/gate.ts#gateBundle', '--out', 'models/gate.generated.ts', '--verify'], fakeRepo)
    expect(fromRoot.status).toBe(0)
    const rootOut = readFileSync(join(subDir, 'gate.generated.ts'), 'utf8')
    expect(rootOut).toContain('// Generated by gdp-wired 0.61.0 from models/gate.ts#gateBundle. Do not edit.')
    expect(rootOut).toContain('// To change behavior, edit the model and its laws, then run from the repository root: npx gdp-wired-cli emit models/gate.ts#gateBundle --out models/gate.generated.ts')

    const stdoutRoot = runCli(['emit', 'models/gate.ts#gateBundle'], fakeRepo)
    const stdoutSub = runCli(['emit', 'gate.ts#gateBundle'], subDir)
    expect(stdoutRoot.status).toBe(0)
    expect(stdoutSub.status).toBe(0)
    expect(stdoutSub.stdout).toBe(stdoutRoot.stdout)

    const checkSub = runCli(['emit', 'gate.ts#gateBundle', '--out', 'gate.generated.ts', '--check', '--verify'], subDir)
    expect(checkSub.status).toBe(0)

    if (existsSync(join(root, '.git'))) {
      const checkExamplesSub = runCli(['emit', 'review-routing.ts#reviewRoutingBundle', '--out', 'review-routing.generated.ts', '--check', '--verify'], join(root, 'examples'))
      expect(checkExamplesSub.status).toBe(0)
    }
  })

  test('CLI --out, --check (pass, 1-char edit diff -> exit 1, missing -> exit 1), --verify, and unproven -> exit 2', async () => {
    const outFile = join(tmp, 'cli-review.generated.ts')
    // Missing file under --check -> exit 1
    expect(runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle', '--out', outFile, '--check']).status).toBe(1)

    // Write + differential --verify -> exit 0
    const writeRun = runCli(['emit', 'examples/review-routing.ts#reviewRoutingBundle', '--out', outFile, '--verify'])
    expect(writeRun.status).toBe(0)
    expect(writeRun.stdout).toContain('verified')
    expect(writeRun.stdout).toContain('differential trials')

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

    // RatRule works end-to-end with CLI --out + --verify (exit 0)
    const ratMod = join(tmp, 'rat-export.ts')
    writeFileSync(ratMod, `
      import {feeSplit, feeLaws} from ${JSON.stringify(join(root, 'examples/rationals.ts'))}
      const r = feeSplit()
      export const bundle = {ratRule: r, laws: feeLaws(r)}
    `)
    const ratVerify = await emitMain([`${ratMod}#bundle`, '--out', join(tmp, 'rat-out.ts'), '--verify'])
    expect(ratVerify).toBe(0)
  })

  test('differential --verify refutes deliberate emitter mutants across Fun, Rule, maps, and RatRule (exit 1)', async () => {
    // 1. Mutants on emitted reviewRouting (Fun with decimals)
    const reviewRes = reviewRouting.emit({laws: reviewRoutingLaws, defaultParams: defaultReviewParams, name: 'reviewRouting'})
    const reviewMutants: [string, string, string][] = [
      ['drop tamper guard', 'args.tamperSuspected ? "reject" :', 'false ? "reject" :'],
      ['flip clearRisk comparison', '$a_risk < $p_clearRisk', '$a_risk <= $p_clearRisk'],
      ['break escalation reject->approve', 'decision === "review"', 'decision === "review" || decision === "reject"'],
      ['corrupt half-even tie-break to half-up', 'firstDrop === \'5\' && (hasMore || odd)', 'firstDrop === \'5\''],
    ]
    for (const [label, from, to] of reviewMutants) {
      expect(reviewRes.source).toContain(from)
      const mutFile = join(tmp, `mut-review-${++seq}.ts`)
      writeFileSync(mutFile, reviewRes.source.replaceAll(from, to))
      const ver = await verifyEmittedFile(mutFile, {kind: 'fun', fun: reviewRouting, defaultParams: defaultReviewParams}, reviewRes)
      expect({label, ok: ver.ok, exit: ver.exit}).toEqual({label, ok: false, exit: 1})
      expect(ver.mismatch).toBeTruthy()
    }

    // 2. Mutant on emitted README budget (drop Math.min cap)
    const budget = rule('budget').params({b: nat, m: nat}).inputs({c: nat}).state({s: 0})
      .step(({b, m, c, s}) => ({s: when(s.lt(b), s.plus(min(c, m)), s)}))
    const bounded = budget.law('spend stays within b + m', ({s, b, m}) => s.atMost(b.plus(m)))
    const budgetRes = budget.emit({laws: [bounded]})
    const mutBudgetFile = join(tmp, `mut-budget-${++seq}.ts`)
    writeFileSync(mutBudgetFile, budgetRes.source.replace('Math.min(input.c, params.m)', 'input.c'))
    const verB = await verifyEmittedFile(mutBudgetFile, {kind: 'rule', rule: budget}, budgetRes)
    expect(verB).toMatchObject({ok: false, exit: 1})
    expect(verB.mismatch).toBeTruthy()

    // 3. Mutant on emitted caps (flip `< params.d` to `<= params.d`)
    const caps = rule('caps').params({d: nat}).inputs({acct: nat, day: nat, ok: bool}).maps({Acct: 0, Day: 0})
      .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
      .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))
    const dayCap = caps.law('day cap', ({Day, d}) => forall(k => Day.at(k).atMost(d)))
    const capsRes = caps.emit({laws: [dayCap]})
    const mutCapsFile = join(tmp, `mut-caps-${++seq}.ts`)
    writeFileSync(mutCapsFile, capsRes.source.replace('< params.d', '<= params.d'))
    const verC = await verifyEmittedFile(mutCapsFile, {kind: 'rule', rule: caps}, capsRes)
    expect(verC).toMatchObject({ok: false, exit: 1})
    expect(verC.mismatch).toBeTruthy()

    // 4. Mutant on emitted RatRule (feeSplit: corrupt 39n/40n payout coefficient)
    const fs = feeSplit()
    const fsRes = fs.emit({laws: feeLaws(fs)})
    expect(fsRes.source).toContain('[39n, 40n]')
    const mutRatFile = join(tmp, `mut-rat-${++seq}.ts`)
    writeFileSync(mutRatFile, fsRes.source.replace('[39n, 40n]', '[39n, 41n]'))
    const verR = await verifyEmittedFile(mutRatFile, {kind: 'ratRule', ratRule: fs}, fsRes)
    expect(verR).toMatchObject({ok: false, exit: 1})
    expect(verR.mismatch).toBeTruthy()
  })
})

// --- Phase 2: 100% enforced expressibility (op-by-op, kind-by-kind, and all runtime features) -----------------------

describe('100% enforced expressibility: every op, kind, and runtime feature', () => {
  test('core/emit.ts has zero "not supported" refusals and covers all canonical op/kind/machine lists', () => {
    const emitSrc = readFileSync(join(root, 'core/emit.ts'), 'utf8')
    expect(emitSrc).not.toMatch(/not supported/i)
    expect(E_OPS.length).toBeGreaterThanOrEqual(12)
    expect(C_OPS.length).toBeGreaterThanOrEqual(8)
    expect(QE_OPS.length).toBeGreaterThanOrEqual(8)
    expect(QC_OPS.length).toBeGreaterThanOrEqual(6)
    expect(KIND_NAMES.length).toBeGreaterThanOrEqual(11)
    expect(MACHINE_PARTS.length).toBeGreaterThanOrEqual(17)
  })

  test('every E op and C op from canonical E_OPS / C_OPS emits and passes --verify', async () => {
    const makeRuleForE = (op: (typeof E_OPS)[number]) => {
      switch (op) {
        case 'const': return rule('op-const').inputs({x: nat}).state({s: 0}).step(() => ({s: 7}))
        case 'var': return rule('op-var').inputs({x: nat}).state({s: 0}).step(({x}) => ({s: x}))
        case 'add': return rule('op-add').inputs({x: nat}).state({s: 0}).step(({x, s}) => ({s: s.plus(x)}))
        case 'sub': return rule('op-sub').inputs({x: nat}).state({s: 10}).step(({x, s}) => ({s: s.minus(x)}))
        case 'mul': return rule('op-mul').inputs({x: nat}).state({s: 0}).step(({x}) => ({s: x.times(3)}))
        case 'prod': return rule('op-prod').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: x.mul(y)}))
        case 'min': return rule('op-min').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: min(x, y)}))
        case 'max': return rule('op-max').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: max(x, y)}))
        case 'if': return rule('op-if').inputs({x: nat}).state({s: 0}).step(({x, s}) => ({s: when(x.lt(5), x, s)}))
        case 'get': return rule('op-get').inputs({k: nat, v: nat}).maps({M: 0}).state({last: 0}).step(({k, v, M}) => ({M: M.set(k, v), last: M.at(k)}))
        case 'tup':
        case 'proj': return rule(`op-${op}`).sorts('Node').inputs({a: nat, b: nat}).relations({R: ['Node', 'Node']}).state({hit: 0})
          .step(({a, b, R}) => ({R: R.each((x, y) => R.has(x, y).or(x.eq(a).and(y.eq(b)))), hit: when(R.has(a, b), 1, 0)}))
      }
    }
    for (const op of E_OPS) {
      const r = makeRuleForE(op)
      const res = emitRule(r, {allowUnproven: true})
      const file = join(tmp, `eop-${op}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'rule', rule: r}, res, {runs: 8, steps: 8})
      expect({op, ok: ver.ok, mismatch: ver.mismatch}).toEqual({op, ok: true, mismatch: undefined})
    }

    const makeRuleForC = (op: (typeof C_OPS)[number]) => {
      switch (op) {
        case '<': return rule('cop-lt').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: when(x.lt(y), 1, 0)}))
        case '<=': return rule('cop-le').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: when(x.atMost(y), 1, 0)}))
        case '=': return rule('cop-eq').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: when(x.eq(y), 1, 0)}))
        case 'and': return rule('cop-and').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: when(x.lt(5).and(y.lt(5)), 1, 0)}))
        case 'or': return rule('cop-or').inputs({x: nat, y: nat}).state({s: 0}).step(({x, y}) => ({s: when(x.lt(5).or(y.lt(5)), 1, 0)}))
        case 'not': return rule('cop-not').inputs({x: nat}).state({s: 0}).step(({x}) => ({s: when(x.lt(5).not(), 1, 0)}))
        case 'flag': return rule('cop-flag').inputs({x: nat}).state({s: 0}).flags(({x}) => ({small: x.lt(5)})).step(({small}) => ({s: when(small, 1, 0)}))
        case 'all': return rule('cop-all').inputs({k: nat, v: nat}).maps({M: 0}).state({ok: 0})
          .flags(({M}) => ({allSmall: everyKey(j => M.at(j).atMost(10))}))
          .step(({k, v, M, allSmall}) => ({M: M.set(k, v), ok: when(allSmall, 1, 0)}))
      }
    }
    for (const op of C_OPS) {
      const r = makeRuleForC(op)
      const res = emitRule(r, {allowUnproven: true})
      const file = join(tmp, `cop-${op.replace(/[^a-z]/g, 'x')}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'rule', rule: r}, res, {runs: 8, steps: 8})
      expect({op, ok: ver.ok, mismatch: ver.mismatch}).toEqual({op, ok: true, mismatch: undefined})
    }
  })

  test('every QE op and QC op from canonical QE_OPS / QC_OPS emits and passes --verify', async () => {
    const makeRatForE = (op: (typeof QE_OPS)[number]) => {
      switch (op) {
        case 'const': return ratRule('qe-const').state({s: 0}).step(() => ({s: '1/3'}))
        case 'var': return ratRule('qe-var').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: x}))
        case 'add': return ratRule('qe-add').inputs({x: rat}).state({s: 0}).step(({x, s}) => ({s: s.plus(x)}))
        case 'sub': return ratRule('qe-sub').inputs({x: rat}).state({s: 0}).step(({x, s}) => ({s: s.minus(x)}))
        case 'mul': return ratRule('qe-mul').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: x.times('0.25')}))
        case 'min': return ratRule('qe-min').inputs({x: nonneg}).state({s: 1}).step(({x, s}) => ({s: rmin(s, x)}))
        case 'max': return ratRule('qe-max').inputs({x: nonneg}).state({s: 0}).step(({x, s}) => ({s: rmax(s, x)}))
        case 'if': return ratRule('qe-if').inputs({x: rat}).state({s: 0}).step(({x, s}) => ({s: rwhen(x.lt(1), x, s)}))
      }
    }
    for (const op of QE_OPS) {
      const r = makeRatForE(op)
      const res = emitRatRule(r, {allowUnproven: true})
      const file = join(tmp, `qe-${op}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'ratRule', ratRule: r}, res, {runs: 8, steps: 8})
      expect({op, ok: ver.ok, mismatch: ver.mismatch}).toEqual({op, ok: true, mismatch: undefined})
    }

    const makeRatForC = (op: (typeof QC_OPS)[number]) => {
      switch (op) {
        case '<=': return ratRule('qc-le').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: rwhen(x.atMost(1), 1, 0)}))
        case '<': return ratRule('qc-lt').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: rwhen(x.lt(1), 1, 0)}))
        case '=': return ratRule('qc-eq').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: rwhen(x.eq(0), 1, 0)}))
        case 'and': return ratRule('qc-and').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: rwhen(x.atLeast(0).and(x.atMost(1)), 1, 0)}))
        case 'or': return ratRule('qc-or').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: rwhen(x.lt(0).or(x.gt(1)), 1, 0)}))
        case 'not': return ratRule('qc-not').inputs({x: rat}).state({s: 0}).step(({x}) => ({s: rwhen(x.eq(0).not(), 1, 0)}))
      }
    }
    for (const op of QC_OPS) {
      const r = makeRatForC(op)
      const res = emitRatRule(r, {allowUnproven: true})
      const file = join(tmp, `qc-${op.replace(/[^a-z]/g, 'x')}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'ratRule', ratRule: r}, res, {runs: 8, steps: 8})
      expect({op, ok: ver.ok, mismatch: ver.mismatch}).toEqual({op, ok: true, mismatch: undefined})
    }
  })

  test('every KindInfo from canonical KIND_NAMES emits and passes --verify', async () => {
    const Rec = record({a: nat, b: bool})
    const Var = variant({off: {}, on: {lvl: nat}})
    const u16 = fixedInt(16, false)
    const makeRuleForKind = (kind: (typeof KIND_NAMES)[number]) => {
      switch (kind) {
        case 'nat': case 'unknown': return rule(`k-${kind}`).inputs({x: nat}).state({s: 0}).step(({x}) => ({s: x}))
        case 'bool': return rule('k-bool').inputs({x: bool}).state({s: bool.from(false)}).step(({x}) => ({s: x}))
        case 'oneOf': return rule('k-oneOf').inputs({x: oneOf('a', 'b', 'c')}).state({s: oneOf('a', 'b', 'c').from('a')}).step(({x}) => ({s: x}))
        case 'int': return rule('k-int').inputs({x: int}).ints({s: 0}).step(({x, s}) => ({s: s.plus(x)}))
        case 'decimal': return rule('k-dec').inputs({x: decimal(2, {round: 'half-even'})}).decimals(2, {s: 0}).step(({x, s}) => ({s: s.plus(x)}))
        case 'maybe': return rule('k-maybe').inputs({x: maybe(nat)}).state({s: maybe(nat).from(null)}).step(({x}) => ({s: x}))
        case 'record': return rule('k-record').inputs({x: Rec}).state({s: Rec.from({a: 0, b: false})}).step(({x}) => ({s: x}))
        case 'variant': return rule('k-variant').inputs({x: Var}).state({s: Var.from({tag: 'off'})}).step(({x}) => ({s: x}))
        case 'str': return rule('k-str').inputs({x: str({like: ['a*']})}).state({hit: 0}).step(({x}) => ({hit: when(x.like('a*'), 1, 0)}))
        case 'fixed': return rule('k-fixed').inputs({x: u16, y: u16}).state({s: u16.from(0)}).step(({x, y}) => ({s: x.plus(y, 'WRAP')}))
      }
    }
    for (const kind of KIND_NAMES) {
      const r = makeRuleForKind(kind)
      const res = emitRule(r, {allowUnproven: true})
      const file = join(tmp, `kind-${kind}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'rule', rule: r}, res, {runs: 8, steps: 8})
      expect({kind, ok: ver.ok, mismatch: ver.mismatch}).toEqual({kind, ok: true, mismatch: undefined})
    }
  })

  test('runtime quantifiers, broadcast record/variant maps, tuple-at-every-key, and tuples in recur pass crossCheck + --verify', async () => {
    // 1. Runtime quantifiers (everyKey, someKey, sizedSort, 2-key join)
    const quantRule = rule('quant-all').params({n: nat}).pre(({n}) => n.atMost(5))
      .inputs({k: nat, v: nat}).maps({M: 0, Tag: 0}).state({allOk: 0, anyHi: 0, finOk: 0, uniq: 0})
      .flags(({n, M, Tag}) => ({
        allSmall: everyKey(j => M.at(j).atMost(10)),
        hasBig: someKey(j => M.at(j).gt(5)),
        finAll: sizedSort('Slot', n).every(j => M.at(j).atMost(8)),
        uniqueTags: everyKey((i, j) => Tag.at(i).eq(Tag.at(j)).implies(i.eq(j))),
      }))
      .step(({k, v, M, Tag, allSmall, hasBig, finAll, uniqueTags}) => ({
        M: M.set(k, v), Tag: Tag.set(k, v),
        allOk: when(allSmall, 1, 0), anyHi: when(hasBig, 1, 0), finOk: when(finAll, 1, 0), uniq: when(uniqueTags, 1, 0),
      }))
    expect(quantRule.crossCheck([]).failure).toBeUndefined()
    const qRes = emitRule(quantRule, {allowUnproven: true})
    const qFile = join(tmp, `quant-all-${++seq}.ts`)
    writeFileSync(qFile, qRes.source)
    expect((await verifyEmittedFile(qFile, {kind: 'rule', rule: quantRule}, qRes, {runs: 10, steps: 10})).ok).toBe(true)

    // 2. Broadcast writes on record and variant maps
    const Acc = record({bal: nat, frozen: bool})
    const Job = variant({idle: {}, active: {step: nat}})
    const bcastRule = rule('bcast-maps').inputs({op: oneOf('set', 'freeze', 'reset'), k: nat, amt: nat})
      .maps({A: Acc.from({bal: 0, frozen: false}), J: Job.from({tag: 'idle'})})
      .step(({op, k, amt, A, J}) => ({
        A: A.each(i => ({
          bal: when(op.is('set').and(i.eq(k)), amt, when(op.is('reset'), 0, A.at(i).bal)),
          frozen: when(op.is('freeze'), yes, when(op.is('reset'), no, A.at(i).frozen)),
        })),
        J: J.each(i => when(op.is('set').and(i.eq(k)), Job.make({tag: 'active', step: amt}), when(op.is('reset'), Job.make({tag: 'idle'}), J.at(i)))),
      }))
    expect(bcastRule.crossCheck([]).failure).toBeUndefined()
    const bRes = emitRule(bcastRule, {allowUnproven: true})
    const bFile = join(tmp, `bcast-maps-${++seq}.ts`)
    writeFileSync(bFile, bRes.source)
    expect((await verifyEmittedFile(bFile, {kind: 'rule', rule: bcastRule}, bRes, {runs: 10, steps: 10})).ok).toBe(true)

    // 3. Tuple keys at every key (relations each/union)
    const relRule = rule('rel-tuple-each').sorts('Node').inputs({op: oneOf('add', 'clear', 'close'), a: nat, b: nat})
      .relations({E: ['Node', 'Node']})
      .step(({op, a, b, E}) => ({
        E: E.each((x, y) => op.is('clear').not().and(
          op.is('add').implies(E.has(x, y).or(x.eq(a).and(y.eq(b)))),
          op.is('close').implies(E.has(x, y).or(E.has(x, a).and(E.has(a, y)))),
        )),
      }))
    const relRes = emitRule(relRule, {allowUnproven: true})
    const relFile = join(tmp, `rel-tuple-each-${++seq}.ts`)
    writeFileSync(relFile, relRes.source)
    expect((await verifyEmittedFile(relFile, {kind: 'rule', rule: relRule}, relRes, {runs: 10, steps: 10})).ok).toBe(true)

    // 4. Recurrence with extra args (tuples in recur & call site)
    const stepSum = recur('stepSum', {args: ['k'], zero: 0, next: (_, prev, {k}) => prev.plus(k)}, {'at least 0': (_, fx) => fx.atLeast(0)})
    const recurRule = rule('recur-tup').fns({stepSum}).inputs({n: upTo(6), k: upTo(5)}).state({out: 0})
      .step(({n, k, stepSum}) => ({out: stepSum(n, k)}))
    const rRes = emitRule(recurRule, {allowUnproven: true})
    const rFile = join(tmp, `recur-tup-${++seq}.ts`)
    writeFileSync(rFile, rRes.source)
    expect((await verifyEmittedFile(rFile, {kind: 'rule', rule: recurRule}, rRes, {runs: 10, steps: 10})).ok).toBe(true)
  })

  test('carries, carriesList, carriesSeq, carriesSeqs, lists, nodes, fold, roseFold, loop, counts, leasts, sums, fixedInt, and exists skolems pass crossCheck + --verify', async () => {
    const verifyRuleCase = async (label: string, r: Parameters<typeof emitRule>[0], opts: Parameters<typeof emitRule>[1] = {allowUnproven: true}) => {
      const res = emitRule(r, opts)
      const file = join(tmp, `feat-${label}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'rule', rule: r}, res, {runs: 10, steps: 10})
      expect({label, ok: ver.ok, mismatch: ver.mismatch}).toEqual({label, ok: true, mismatch: undefined})
    }

    // Plain carries map + counts + sums
    const carriedCounts = rule('carried-counts').params({n: nat}).pre(({n}) => n.atMost(5))
      .inputs({k: nat}).carries('S').maps({M: 0})
      .counts({hits: ({n, M, S}) => ({below: n, body: (x, i) => M.at(i).plus(S.at(i)).eq(x.plus(1))})})
      .state({c0: 0})
      .step(({k, M, S, hits}) => ({M: M.set(k, when(S.has(k), 1, M.at(k))), c0: hits.at(0)}))
    expect(carriedCounts.crossCheck([]).failure).toBeUndefined()
    await verifyRuleCase('carried-counts', carriedCounts)

    const seatsSum = rule('seats-sum-rt').params({cap: nat}).inputs({op: oneOf('book', 'cancel'), seat: nat}).maps({Taken: 0})
      .flags(({op, seat, cap, Taken}) => ({books: op.is('book').and(Taken.at(seat).eq(0), Taken.sum().lt(cap)), cancels: op.is('cancel')}))
      .step(({seat, Taken, books, cancels}) => ({Taken: Taken.set(seat, when(books, 1, when(cancels, 0, Taken.at(seat))))}))
    expect(seatsSum.crossCheck([]).failure).toBeUndefined()
    await verifyRuleCase('seats-sum', seatsSum)

    // Lists, nodes, carriesList, carriesSeq, carriesSeqs, leasts (orderbook), exists skolems, fixedInt word division
    const sc = scopeList()
    expect(sc.crossCheck(scopeLaws(sc)).failure).toBeUndefined()
    await verifyRuleCase('lists-scope', sc, {laws: scopeLaws(sc)})

    const st = searchTree()
    expect(st.crossCheck(searchTreeLaws(st)).failure).toBeUndefined()
    await verifyRuleCase('nodes-searchTree', st, {laws: searchTreeLaws(st)})

    const sh = sheet()
    expect(sh.crossCheck(sheetLaws(sh)).failure).toBeUndefined()
    await verifyRuleCase('nodes-sheet', sh, {laws: sheetLaws(sh)})

    const inv = invoices()
    expect(inv.crossCheck(invoiceLaws(inv)).failure).toBeUndefined()
    await verifyRuleCase('carriesList-invoices', inv, {laws: invoiceLaws(inv)})

    const met = metered()
    expect(met.crossCheck(meteredLaws(met)).failure).toBeUndefined()
    await verifyRuleCase('carriesList-metered', met, {laws: meteredLaws(met)})

    const ob = orderBook()
    await verifyRuleCase('leasts-orderbook', ob, {laws: bookLaws(ob)})

    const pat = scopePatterns()
    await verifyRuleCase('carriesSeq-patterns', pat)
    const gr = scopeGrants()
    await verifyRuleCase('carriesSeqs-grants', gr)

    const exL = existsLedger()
    await verifyRuleCase('exists-ledger', exL, {laws: existsLedgerLaws(exL)})

    const u8 = fixedInt(8, false)
    const fxDiv = rule('fx-div').inputs({a: u8, b: u8}).state({q: u8.from(0), rem: u8.from(0)})
      .step(({a, b}) => ({q: a.div(b, 'TRUNCATING', 'TRAP'), rem: a.rem(b, 'TRUNCATING', 'TRAP')}))
    await verifyRuleCase('fixed-worddiv', fxDiv)

    // Binary folds & RoseFold
    for (const [label, f, ls] of [
      ['rollup', rollup(), rollupLaws()],
      ['signoffs', signoffs(), signoffLaws()],
      ['orgChart', orgChart(), orgChartLaws()],
    ] as const) {
      expect(f.crossCheck(ls).failure).toBeUndefined()
      const res = emitFold(f, {laws: ls})
      expect(res.allProven).toBe(true)
      const file = join(tmp, `fold-${label}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'fold', fold: f}, res, {trials: 60})
      expect({label, ok: ver.ok, mismatch: ver.mismatch}).toEqual({label, ok: true, mismatch: undefined})
    }

    // Loops
    for (const [label, lp] of [
      ['pagesNonEmpty', pagesNonEmpty],
      ['retryCapped', retryCapped],
      ['sweepOnce', sweepOnce],
    ] as const) {
      const res = emitLoop(lp)
      expect(res.allProven).toBe(true)
      const file = join(tmp, `loop-${label}-${++seq}.ts`)
      writeFileSync(file, res.source)
      const ver = await verifyEmittedFile(file, {kind: 'loop', loop: lp}, res, {runs: 15, steps: 15})
      expect({label, ok: ver.ok, mismatch: ver.mismatch}).toEqual({label, ok: true, mismatch: undefined})
    }

    // Custom FoldRule + LoopRule via builder
    const customFold = fold('sum-tree').inputs({v: nat}).leaf(({v}) => ({s: v})).node(({v}, l, r) => ({s: l.s.plus(r.s).plus(v)}))
    const cfRes = customFold.emit({laws: [customFold.law('nonneg', ({s}) => s.atLeast(0))]})
    const cfFile = join(tmp, `cfold-${++seq}.ts`)
    writeFileSync(cfFile, cfRes.source)
    expect((await verifyEmittedFile(cfFile, {kind: 'fold', fold: customFold}, cfRes, {trials: 40})).ok).toBe(true)

    const customLoop = loop('countdown').params({n: nat}).state({i: ({n}) => n}).while(({i}) => i.gt(0)).body(({i}) => ({i: i.minus(1)})).rank(({i}) => i)
    const clRes = customLoop.emit()
    const clFile = join(tmp, `cloop-${++seq}.ts`)
    writeFileSync(clFile, clRes.source)
    expect((await verifyEmittedFile(clFile, {kind: 'loop', loop: customLoop}, clRes, {runs: 10, steps: 15})).ok).toBe(true)
  })
})
