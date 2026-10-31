// An order book as keyed maps and least keys (core/dsl.ts's least): a continuous double auction of single units, each
// resting order a cell (present, its price, its arrival, its trader) keyed by the order's id, and the best bid and best
// ask the least keys by price (the highest bid first) and then by arrival. For the suite (`bun examples/orderbook.ts`)
// and core/orderbook.test.ts.
//   - price-time priority: an ask that trades fills the best bid (no bid higher, none at its price earlier), a bid the
//     best ask, as laws of one step over every two orders
//   - the book never crosses: every bid below every ask, a law about every two keys, inductive through the least keys'
//     assumption alone
//   - broken variants: bids ranked by the lowest price (both laws refuted), and arrival ignored at a price (the priority
//     law refuted: two orders at one price, the later one filled)
import {type Law} from '../core/machine.ts'
import {type StepLaw} from '../kernel/kernel.ts'
import {type Term, bool, desc, forall, lit, nat, no, oneOf, proveSteps, record, rule, when, yes} from '../core/dsl.ts'

export const Order = record({has: bool, price: nat, seq: nat, who: nat})
const empty = {has: false, price: 0, seq: 0, who: 0}, none = {has: no, price: lit(0), seq: lit(0), who: lit(0)}
export type Bug = 'bids by the lowest price' | 'ignores arrival'
export const book = (bug?: Bug) => rule('order book')
  .inputs({op: oneOf('bid', 'ask', 'cancel'), id: nat, price: nat, who: nat})
  .state({seq: 0})
  .maps({Bids: Order.from(empty), Asks: Order.from(empty)})
  .least({
    bestBid: ({Bids}) => ({where: k => Bids.at(k).has, by: k => [bug === 'bids by the lowest price' ? Bids.at(k).price : desc(Bids.at(k).price), ...(bug === 'ignores arrival' ? [] : [Bids.at(k).seq])]}),
    bestAsk: ({Asks}) => ({where: k => Asks.at(k).has, by: k => [Asks.at(k).price, ...(bug === 'ignores arrival' ? [] : [Asks.at(k).seq])]}),
  })
  // A new order's id is one no resting order has.
  .assume(({op, id, Bids, Asks}) => op.is('cancel').or(Bids.at(id).has.not().and(Asks.at(id).has.not())))
  .flags(({op, price, bestBid, bestAsk, Bids, Asks}) => ({
    lifts: op.is('bid').and(bestAsk.isSome, Asks.at(bestAsk.inner).price.atMost(price)),
    hits: op.is('ask').and(bestBid.isSome, price.atMost(Bids.at(bestBid.inner).price)),
  }))
  .step(({op, id, price, who, seq, bestBid, bestAsk, lifts, hits, Bids, Asks}) => {
    const fresh = {has: yes, price, seq, who}
    const side = (map: typeof Bids, mine: 'bid' | 'ask', filled: typeof lifts, best: Term) => map.set(when(filled, best, id), when(filled.or(op.is('cancel')), none, when(op.is(mine).and((mine === 'bid' ? lifts : hits).not()), fresh, map.at(id))))
    return {seq: seq.plus(1), Bids: side(Bids, 'bid', hits, bestBid.inner), Asks: side(Asks, 'ask', lifts, bestAsk.inner)}
  })

type Book = ReturnType<typeof book>
export const bookLaws = (r: Book = book()): Law[] => [
  ...r.kindLaws(),
  r.law('the book never crosses', ({Bids, Asks}) => forall((b, a) => Bids.at(b).has.and(Asks.at(a).has).implies(Bids.at(b).price.lt(Asks.at(a).price)))),
]
export const bookSteps = (r: Book = book()): StepLaw[] => [
  r.stepLaw('an ask fills the best bid: none higher, none at its price earlier', ({op, Bids}, after) => forall((k, j) =>
    op.is('ask').and(Bids.at(k).has, after.Bids.at(k).has.not(), Bids.at(j).has).implies(
      Bids.at(j).price.lt(Bids.at(k).price).or(Bids.at(j).price.eq(Bids.at(k).price).and(Bids.at(k).seq.atMost(Bids.at(j).seq)))))),
  r.stepLaw('a bid fills the best ask: none lower, none at its price earlier', ({op, Asks}, after) => forall((k, j) =>
    op.is('bid').and(Asks.at(k).has, after.Asks.at(k).has.not(), Asks.at(j).has).implies(
      Asks.at(k).price.lt(Asks.at(j).price).or(Asks.at(k).price.eq(Asks.at(j).price).and(Asks.at(k).seq.atMost(Asks.at(j).seq)))))),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'bids by the lowest price', 'ignores arrival'] as const) {
    const r = book(bug), v = proveSteps(r, bookLaws(r), bookSteps(r))
    results.push([`order book${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
