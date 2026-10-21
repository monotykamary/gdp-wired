// The nonlinear track's corpus: laws with products of unknowns that gdp-wired's prover didn't prove before 0.15 (at
// eb28edc), each true, and none with anything stated beyond the law. Products of a map's cell (a per-key quota, a cost
// kept as price times quantity), and refutations that need squares: Cauchy–Schwarz, AM–GM for three, shares of a fixed
// total, cubes. `today` is the library itself: the track's search is the prover's. Each law is checked on random
// values too (`bun research/frontier/nonlinear.ts`), apart from the prover.
import {type Verdict, forall, fun, nat, oneOf, proveDecision, proveRule, rule, when} from '../../core/dsl.ts'
import type {Item} from './corpus.ts'

const quota = () => rule('per-key quota').params({per: nat}).inputs({op: oneOf('join', 'use'), k: nat, amt: nat}).state({}).maps({Seats: 0, Used: 0})
  .step(({op, k, amt, per, Seats, Used}) => ({
    Seats: Seats.set(k, when(op.is('join'), Seats.at(k).plus(1), Seats.at(k))),
    Used: Used.set(k, when(op.is('use').and(Used.at(k).plus(amt).atMost(per.mul(Seats.at(k)))), Used.at(k).plus(amt), Used.at(k))),
  }))
const orders = () => rule('orders').inputs({op: oneOf('add', 'price'), k: nat, n: nat}).state({}).maps({Price: 0, Qty: 0, Cost: 0})
  .step(({op, k, n, Price, Qty, Cost}) => ({
    Qty: Qty.set(k, when(op.is('add'), Qty.at(k).plus(n), Qty.at(k))),
    Cost: Cost.set(k, when(op.is('add'), Cost.at(k).plus(n.mul(Price.at(k))), when(op.is('price'), Qty.at(k).mul(n), Cost.at(k)))),
    Price: Price.set(k, when(op.is('price'), n, Price.at(k))),
  }))
const accounts = () => rule('accounts').inputs({op: oneOf('day', 'spend', 'raise'), k: nat, n: nat}).state({}).maps({Rate: 0, Days: 0, Spent: 0})
  .step(({op, k, n, Rate, Days, Spent}) => ({
    Days: Days.set(k, when(op.is('day'), Days.at(k).plus(1), Days.at(k))),
    Spent: Spent.set(k, when(op.is('spend').and(Spent.at(k).plus(n).atMost(Rate.at(k).mul(Days.at(k)))), Spent.at(k).plus(n), Spent.at(k))),
    Rate: Rate.set(k, when(op.is('raise').and(n.gt(Rate.at(k))), n, Rate.at(k))),
  }))
// Two shares of a fixed total, one moved at a time: their product is at most total²/4.
const shares = () => rule('shares').params({total: nat}).inputs({op: oneOf('move', 'back')}).state({a: 0, b: ({total}) => total})
  .step(({op, a, b}) => ({a: when(op.is('move').and(b.gt(0)), a.plus(1), when(op.is('back').and(a.gt(0)), a.minus(1), a)), b: when(op.is('move').and(b.gt(0)), b.minus(1), when(op.is('back').and(a.gt(0)), b.plus(1), b))}))
// Running statistics: the sum of the samples squared is at most their count times the sum of their squares.
const stats = () => rule('running statistics').inputs({v: nat}).state({n: 0, s: 0, q: 0}).step(({v, n, s, q}) => ({n: n.plus(1), s: s.plus(v), q: q.plus(v.mul(v))}))

const four = fun('four').inputs({a: nat, b: nat, c: nat, d: nat}).returns(({a, b, c, d}) => ({l: a.mul(c).plus(b.mul(d)), x: a.mul(a).plus(b.mul(b)), y: c.mul(c).plus(d.mul(d))}))
const three = fun('three').inputs({a: nat, b: nat, c: nat}).returns(({a, b, c}) => ({cubes: a.mul(a).mul(a).plus(b.mul(b).mul(b)).plus(c.mul(c).mul(c)), abc: a.mul(b).mul(c)}))
const two = fun('two').inputs({a: nat, b: nat}).returns(({a, b}) => ({a3: a.mul(a).mul(a), b3: b.mul(b).mul(b)}))

const rand = (() => { let x = 7; return (k: number) => { x = (x * 1103515245 + 12345) % 2 ** 31; return Math.floor(x / 2 ** 31 * k) } })()
// Each item: the law through the library, and the same law on random values (a run of the rule, or the arithmetic).
type Case = Item & {holds: () => boolean, proven: boolean}
const sample = (n: number, f: (r: (k: number) => number) => boolean) => Array.from({length: n}, () => f(rand)).every(Boolean)
const runs = (steps: number, start: Record<string, number>, step: (s: Record<string, number>, r: (k: number) => number) => void, law: (s: Record<string, number>) => boolean) =>
  sample(200, r => { const s = {...start}; for (let i = 0; i < steps; i++) { step(s, r); if (!law(s)) return false } return true })

const item = (id: string, removed: string, today: () => Verdict, holds: () => boolean, proven = true): Case => ({id: `nonlinear/${id}`, track: 'nonlinear', removed, today, holds, proven})
export const cases: Case[] = [
  item('per-key quota', 'nothing: a cell times a param', () => { const r = quota(); return proveRule(r, [r.law('every key: used within per × seats', ({Used, Seats, per}) => forall(k => Used.at(k).atMost(per.mul(Seats.at(k)))))]) },
    () => sample(200, r => { const per = r(5), S = [0, 0, 0], U = [0, 0, 0]; for (let i = 0; i < 30; i++) { const k = r(3), amt = r(6); if (r(2)) S[k]!++; else if (U[k]! + amt <= per * S[k]!) U[k]! += amt; if (U.some((u, j) => u > per * S[j]!)) return false } return true })),
  item('orders', 'nothing: a cell times a cell', () => { const r = orders(); return proveRule(r, [r.law('every key: cost is price × quantity', ({Cost, Price, Qty}) => forall(k => Cost.at(k).eq(Price.at(k).mul(Qty.at(k)))))]) },
    () => sample(200, r => { const P = [0, 0], Q = [0, 0], C = [0, 0]; for (let i = 0; i < 30; i++) { const k = r(2), n = r(9); if (r(2)) { Q[k]! += n; C[k]! += n * P[k]! } else { P[k] = n; C[k] = Q[k]! * n } if (C.some((c, j) => c !== P[j]! * Q[j]!)) return false } return true })),
  item('accounts', 'nothing: a cell times a cell', () => { const r = accounts(); return proveRule(r, [r.law('every key: spent within rate × days', ({Spent, Rate, Days}) => forall(k => Spent.at(k).atMost(Rate.at(k).mul(Days.at(k)))))]) },
    () => sample(200, r => { const R = [0, 0], D = [0, 0], Sp = [0, 0]; for (let i = 0; i < 30; i++) { const k = r(2), n = r(9), op = r(3); if (op === 0) D[k]!++; else if (op === 1) { if (Sp[k]! + n <= R[k]! * D[k]!) Sp[k]! += n } else if (n > R[k]!) R[k] = n; if (Sp.some((s, j) => s > R[j]! * D[j]!)) return false } return true })),
  item('shares', 'nothing: (a − b + 2)² after a move', () => { const r = shares(); return proveRule(r, [r.law('the shares sum to the total', ({a, b, total}) => a.plus(b).eq(total)), r.law('4ab within total²', ({a, b, total}) => a.mul(b).times(4).atMost(total.mul(total)))]) },
    () => sample(200, r => { const t = r(20); let a = 0, b = t; for (let i = 0; i < 40; i++) { if (r(2)) { if (b > 0) { a++; b-- } } else if (a > 0) { a--; b++ } if (4 * a * b > t * t) return false } return true })),
  item('cauchy-schwarz', 'nothing: (ad − bc)²', () => proveDecision(four.law('(ac + bd)² <= (a² + b²)(c² + d²)', () => [], o => o.l.mul(o.l).atMost(o.x.mul(o.y)))),
    () => sample(2000, r => { const [a, b, c, d] = [r(50), r(50), r(50), r(50)]; return (a * c + b * d) ** 2 <= (a * a + b * b) * (c * c + d * d) })),
  item('am-gm for three', 'nothing: a·(b − c)² and the like', () => proveDecision(three.law('3abc <= a³ + b³ + c³', () => [], o => o.abc.times(3).atMost(o.cubes))),
    () => sample(2000, r => { const [a, b, c] = [r(50), r(50), r(50)]; return 3 * a * b * c <= a ** 3 + b ** 3 + c ** 3 })),
  item('cubes', 'nothing: products of a row with squares', () => proveDecision(two.law('a³ <= b³ only when a <= b', () => [], (o, {a, b}) => o.a3.atMost(o.b3).implies(a.atMost(b)))),
    () => sample(2000, r => { const [a, b] = [r(50), r(50)]; return a ** 3 > b ** 3 || a <= b })),
  // Not yet: the certificate multiplies the goal by n before (n·v − s)² closes it, a multiplier no square here suggests.
  item('running statistics', 'not proven: needs n times the goal', () => { const r = stats(); return proveRule(r, [r.law('s² within n·q', ({n, s, q}) => s.mul(s).atMost(n.mul(q)))]) },
    () => runs(20, {n: 0, s: 0, q: 0}, (s, r) => { const v = r(30); s.n!++; s.s! += v; s.q! += v * v }, s => s.s! * s.s! <= s.n! * s.q!), false),
]
export const nonlinear: Item[] = cases.map(c => ({id: c.id, track: c.track, removed: c.removed, today: c.today}))

if (import.meta.main) {
  let bad = 0
  for (const c of cases) {
    const t = performance.now(), v = c.today(), ms = Math.round(performance.now() - t), ok = v.proven && v.checked, holds = c.holds()
    const fine = holds && ok === c.proven
    if (!fine) bad++
    console.log(`${fine ? 'ok  ' : 'FAIL'} ${c.id}: ${ok ? `proven ${ms} ms` : `not proven (${v.goal ?? ''} ${v.stuck ?? ''})`}, ${holds ? 'holds on random values' : 'BROKEN on random values'}`)
  }
  if (bad) process.exit(1)
}
