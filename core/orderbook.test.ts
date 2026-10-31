// Least keys (core/dsl.ts's least, core/machine.ts's leastsIn): examples/orderbook.ts's book proven (price-time
// priority, never crossed) and each broken variant refuted; the runtimes find the least keys a scan of the book finds,
// the interpreter and the compiled code alike, and every request with a fresh id is allowed.
import {expect, test} from 'bun:test'
import {book, bookLaws, bookSteps} from '../examples/orderbook.ts'
import {desc, nat, proveSteps, rule} from './dsl.ts'
import {allowed} from './watch.ts'

test('price-time priority and a book that never crosses: proven; each broken variant refuted', () => {
  const r = book()
  expect(proveSteps(r, bookLaws(r), bookSteps(r))).toMatchObject({proven: true, checked: true})
  for (const bug of ['bids by the lowest price', 'ignores arrival'] as const) {
    const b = book(bug)
    expect(proveSteps(b, bookLaws(b), bookSteps(b)).proven).toBe(false)
  }
}, 300_000)

test('the least keys: found as a scan of the book finds them, by the interpreter and the compiled code alike', () => {
  let x = 11
  const rand = (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) }
  const r = book(), m = r.machine, run = r.interpreter(), gen = r.compiled(), ps = r.encodeParams({})
  expect(Object.keys(m.leasts!)).toEqual(['bestBid', 'bestAsk'])
  let trades = 0
  for (let t = 0; t < 200; t++) {
    let st = run.init(ps), g = gen.init(ps), id = 1
    for (let i = 0; i < 12; i++) {
      const book0 = r.decode(st) as unknown as {Bids: Record<string, {has: boolean, price: number, seq: number}>, Asks: Record<string, {has: boolean, price: number, seq: number}>}
      const scan = (side: Record<string, {has: boolean, price: number, seq: number}>, high: boolean) => {
        const live = Object.entries(side).filter(([, o]) => o.has).map(([k, o]) => ({k: Number(k), ...o}))
        live.sort((a, b) => (a.price !== b.price ? (high ? b.price - a.price : a.price - b.price) : a.seq !== b.seq ? a.seq - b.seq : a.k - b.k))
        return live[0]?.k
      }
      const op = (['bid', 'ask', 'cancel'] as const)[rand(3)]!, held = [...Object.keys(book0.Bids), ...Object.keys(book0.Asks)]
      const input = r.encodeInput({op, id: op === 'cancel' && held.length ? Number(held[rand(held.length)]) : id++, price: rand(6), who: rand(3)})
      expect(allowed(m, run, ps, st, input)).toBe(true)
      const found = run.queries(ps, st, input)
      expect([found.bestBid$some ? found.bestBid : undefined, found.bestAsk$some ? found.bestAsk : undefined]).toEqual([scan(book0.Bids, true), scan(book0.Asks, false)])
      const before = Object.values(book0.Bids).filter(o => o.has).length + Object.values(book0.Asks).filter(o => o.has).length
      st = run.step(ps, st, input); g = gen.step(ps, g, input)
      expect(r.decode(g)).toEqual(r.decode(st))
      const now = r.decode(st) as unknown as typeof book0
      if (Object.values(now.Bids).filter(o => o.has).length + Object.values(now.Asks).filter(o => o.has).length < before && op !== 'cancel') trades++
    }
  }
  expect(trades).toBeGreaterThan(100)
})

test('a least key whose condition holds past every cell has none: the request is refused', () => {
  const r = rule('everywhere').inputs({n: nat}).maps({M: 0}).least({low: ({M}) => ({where: k => M.at(k).atMost(0), by: k => [desc(k)]})}).state({x: 0}).step(({low, x}) => ({x: low.inner.plus(x)}))
  const run = r.interpreter(), ps = r.encodeParams({})
  expect(() => run.step(ps, run.init(ps), r.encodeInput({n: 1}))).toThrow(/no least/)
})
