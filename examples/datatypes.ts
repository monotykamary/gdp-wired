// Records and variants: a payment is by card (an amount, the last four digits, verified or not), in cash or by voucher,
// and a customer is a record (a tier, a limit, blocked or not); a hold is a variant kept as state (idle, holding an amount
// since a time, released). For the suite (`bun examples/datatypes.ts`), core/datatypes.test.ts and
// lean-kernel/package-check.ts.
//   - approve: who may pay how much, by each way of paying; the broken variant approves unverified cards
//   - hold: funds held up to a cap and released only once the wait is over; the broken variant releases early
//   - accounts: a map of records (a limit, what is spent, frozen or not); nothing spent past its limit, and a frozen
//     account spends nothing; the broken variant lowers a limit below what is spent
//   - seats: a map of variants (free, held by someone until a time, sold to someone); a sale is final; the broken
//     variant lets a hold replace a sale
//   - jobs: a list of records (an id, a priority) of at most cap items; a push puts its job last; the broken variant
//     pushes past the cap
import {type Choice, type Term, bool, forall, fun, nat, no, oneOf, proveDecision, proveSteps, record, rule, same, upTo, variant, when, yes} from '../core/dsl.ts'

export const payment = variant({card: {amount: nat, last4: upTo(9999), verified: bool}, cash: {amount: nat}, voucher: {cover: upTo(100)}})
export const customer = record({tier: oneOf('basic', 'gold'), limit: nat, blocked: bool})
const ceiling = (tier: Choice<'basic' | 'gold'>, limit: Term) => tier.match({basic: () => limit, gold: () => limit.plus(500)})
export const approve = (bug?: 'approves unverified cards') => fun('approve a payment')
  .inputs({pay: payment, who: customer})
  .returns(({pay, who}) => ({
    ok: who.blocked.not().and(pay.match({
      card: c => c.amount.atMost(ceiling(who.tier, who.limit)).and(bug ? yes : c.verified),
      cash: c => c.amount.atMost(200),
      voucher: () => who.tier.is('gold'),
    })),
    charged: pay.match({card: c => c.amount, cash: c => c.amount, voucher: () => 0}),
  }))
export const approveLaws = (f = approve()) => [
  f.law('a blocked customer is never approved', ({who}, out) => [who.blocked, out.ok], () => no),
  f.law('an unverified card is never approved', ({pay}, out) => [pay.match({card: c => c.verified.not(), cash: () => no, voucher: () => no}), out.ok], () => no),
  f.law('an approved charge is within the ceiling, or cash up to 200', ({pay}, out) => [out.ok, pay.is('voucher').not()],
    (out, {pay, who}) => out.charged.atMost(ceiling(who.tier, who.limit)).or(pay.is('cash').and(out.charged.atMost(200)))),
  f.law('a voucher charges nothing', ({pay}) => pay.is('voucher'), out => out.charged.eq(0)),
]

export const Held = variant({idle: {}, holding: {amount: nat, since: nat}, released: {amount: nat}})
export const hold = (bug?: 'releases early') => rule('hold and release')
  .params({cap: nat, wait: nat})
  .inputs({op: oneOf('hold', 'release', 'refund'), amount: nat, now: nat})
  .state({at: Held.from({tag: 'idle'}), paid: 0})
  .flags(({op, amount, at, now, wait, cap}) => ({
    held: op.is('hold').and(at.is('idle'), amount.atMost(cap), amount.gt(0)),
    freed: op.is('release').and(at.match({holding: h => (bug ? h.since : h.since.plus(wait)).atMost(now), idle: () => no, released: () => no})),
    back: op.is('refund').and(at.is('holding')),
  }))
  .step(({amount, now, at, held, freed, back, paid}) => ({
    at: when(held, Held.make({tag: 'holding', amount, since: now}),
      when(freed, at.match({holding: h => Held.make({tag: 'released', amount: h.amount}), idle: () => at, released: () => at}), when(back, Held.make({tag: 'idle'}), at))),
    paid: when(freed, paid.plus(at.match({holding: h => h.amount, idle: () => 0, released: () => 0})), paid),
  }))
export const holdLaws = (r = hold()) => [
  r.law('the case is one of three', ({at}) => at.is('idle').or(at.is('holding'), at.is('released'))),
  r.law('a hold is within the cap', ({at, cap}) => at.match({holding: h => h.amount.atMost(cap), released: rel => rel.amount.atMost(cap), idle: () => yes})),
  r.law('what is paid is what was released', ({at, paid}) => at.match({released: rel => paid.eq(rel.amount), idle: () => paid.eq(0), holding: () => paid.eq(0)})),
]
export const holdSteps = (r = hold()) => [
  r.stepLaw('a release happens only once the wait is over',
    (b, after) => after.at.is('released').and(b.at.is('released').not()).implies(b.at.match({holding: h => h.since.plus(b.wait).atMost(b.now), idle: () => no, released: () => no}))),
]

export const Account = record({limit: nat, spent: nat, frozen: bool})
export const accounts = (bug?: 'lowers a limit below what is spent') => rule('accounts')
  .inputs({op: oneOf('limit', 'spend', 'freeze'), who: nat, amount: nat})
  .maps({Acct: Account.from({limit: 0, spent: 0, frozen: false})})
  .flags(({op, who, amount, Acct}) => ({
    spends: op.is('spend').and(Acct.at(who).frozen.not(), Acct.at(who).spent.plus(amount).atMost(Acct.at(who).limit)),
    limits: op.is('limit').and(bug ? yes : Acct.at(who).spent.atMost(amount)),
  }))
  .step(({op, who, amount, spends, limits, Acct}) => {
    const a = Acct.at(who)
    return {Acct: Acct.set(who, {limit: when(limits, amount, a.limit), spent: when(spends, a.spent.plus(amount), a.spent), frozen: a.frozen.or(op.is('freeze'))})}
  })
export const accountLaws = (r = accounts()) => [r.law('nothing is spent past its limit', ({Acct}) => forall(k => Acct.at(k).spent.atMost(Acct.at(k).limit)))]
export const accountSteps = (r = accounts()) => [
  r.stepLaw('a frozen account spends nothing', ({Acct}, after) => forall(k => Acct.at(k).frozen.implies(after.Acct.at(k).spent.eq(Acct.at(k).spent)))),
]

export const Seat = variant({free: {}, held: {by: nat, until: nat}, sold: {to: nat}})
export const seats = (bug?: 'lets a hold replace a sale') => rule('seats')
  .inputs({op: oneOf('hold', 'buy'), seat: nat, who: nat, now: nat})
  .maps({Seats: Seat.from({tag: 'free'})})
  .flags(({op, seat, who, now, Seats}) => {
    const s = Seats.at(seat), lapsed = s.match({free: () => yes, held: h => h.until.lt(now), sold: () => no})
    return {
      holds: op.is('hold').and(bug ? s.is('held').not().or(lapsed) : lapsed),
      buys: op.is('buy').and(s.match({free: () => yes, held: h => h.by.eq(who).or(h.until.lt(now)), sold: () => no})),
    }
  })
  .step(({seat, who, now, holds, buys, Seats}) => ({
    Seats: Seats.set(seat, when(holds, Seat.make({tag: 'held', by: who, until: now.plus(10)}), when(buys, Seat.make({tag: 'sold', to: who}), Seats.at(seat)))),
  }))
export const seatLaws = (r = seats()) => [r.law('every seat is free, held or sold', ({Seats}) => forall(k => Seats.at(k).is('free').or(Seats.at(k).is('held'), Seats.at(k).is('sold'))))]
export const seatSteps = (r = seats()) => [
  r.stepLaw('a sale is final', ({Seats}, after) => forall(k => Seats.at(k).match({sold: s => after.Seats.at(k).match({sold: t => t.to.eq(s.to), free: () => no, held: () => no}), free: () => yes, held: () => yes}))),
]

export const Job = record({id: nat, prio: upTo(9)})
export const jobs = (bug?: 'pushes past the cap') => rule('jobs')
  .params({cap: nat})
  .inputs({op: oneOf('push', 'pop'), job: Job})
  .items({Queue: Job})
  .step(({op, job, cap, Queue, Queue_len}) => Queue.apply(Queue.push(job, op.is('push').and(bug ? yes : Queue_len.lt(cap))), Queue.pop(op.is('pop').and(Queue_len.gt(0)))))
export const jobLaws = (r = jobs()) => [
  r.law('at most cap jobs', ({Queue_len, cap}) => Queue_len.atMost(cap)),
  r.law('nothing past the end', ({Queue}) => Queue.within()),
]
export const jobSteps = (r = jobs()) => [
  r.stepLaw('a push puts its job last', ({job, Queue_len}, after) => same(after.Queue.at(Queue_len), job), ({op, cap, Queue_len}) => op.is('push').and(Queue_len.lt(cap))),
]

if (import.meta.main) {
  const results: [string, boolean, boolean][] = []
  for (const bug of [undefined, 'approves unverified cards'] as const) {
    const f = approve(bug)
    results.push([`approve a payment${bug ? ` (${bug})` : ''}`, approveLaws(f).every(d => { const v = proveDecision(d); return v.proven && v.checked }), !bug])
  }
  for (const bug of [undefined, 'releases early'] as const) {
    const r = hold(bug), v = proveSteps(r, holdLaws(r), holdSteps(r))
    results.push([`hold and release${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'lowers a limit below what is spent'] as const) {
    const r = accounts(bug), v = proveSteps(r, accountLaws(r), accountSteps(r))
    results.push([`accounts${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'lets a hold replace a sale'] as const) {
    const r = seats(bug), v = proveSteps(r, seatLaws(r), seatSteps(r))
    results.push([`seats${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const bug of [undefined, 'pushes past the cap'] as const) {
    const r = jobs(bug), v = proveSteps(r, jobLaws(r), jobSteps(r))
    results.push([`jobs${bug ? ` (${bug})` : ''}`, v.proven && v.checked, !bug])
  }
  for (const [name, got, want] of results) console.log(`${got === want ? 'ok  ' : 'FAIL'} ${name}: ${got ? 'proven' : 'refused'}`)
  if (results.some(([, got, want]) => got !== want)) process.exit(1)
}
