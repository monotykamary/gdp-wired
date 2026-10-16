// Synthesis problems: machines whose law needs an invariant nobody wrote, and loops whose rank nobody wrote.
import {type Law, type Machine, all, any, atMost, ite, less, min, minus, n, plus, same, times, x} from '../core/machine.ts'
import {inflight, inflightLoss} from '../core/models.ts'
import type {Loop} from '../kernel/kernel.ts'
import type {Box, Form} from './compile.ts'

const range = (a: number, b: number) => Array.from({length: b - a + 1}, (_, i) => a + i)
const signed = (cs: number[]) => [...cs, ...cs.map(c => -c)]

export type InvariantCase = {what: string, depth: number, history: Box, m: Machine, goal: Law, goalForm: Form, box: Box, small: Box, coefs: number[], consts: number[], terms: number}
export type RankCase = {what: string, l: Loop, laws: Law[], box: Box, small: Box, coefs: number[], consts: number[], terms: number}

// A token bucket: 3 tokens a tick up to 10, a request spends what it can. Spending is bounded by 10 + 3 per tick, which
// needs tokens + spent <= 10 + 3·ticks (three variables, a coefficient of -3).
const bucket: Machine = {
  name: 'token bucket', params: [], inputs: ['kind', 'amt'], state: {tokens: n(10), spent: n(0), ticks: n(0)},
  step: {state: {
    tokens: ite(same(x('kind'), n(0)), min(plus(x('tokens'), n(3)), n(10)), minus(x('tokens'), min(x('amt'), x('tokens')))),
    spent: ite(same(x('kind'), n(0)), x('spent'), plus(x('spent'), min(x('amt'), x('tokens')))),
    ticks: ite(same(x('kind'), n(0)), plus(x('ticks'), n(1)), x('ticks')),
  }},
  assume: atMost(x('kind'), n(1)),
}
// A leaky bucket with its capacity B a param: a tick drains 2, a request is admitted while the level is under B.
// admitted <= B + 2·ticks needs admitted <= level + 2·ticks and level <= B.
const leaky: Machine = {
  name: 'leaky bucket', params: ['B'], inputs: ['kind'], state: {level: n(0), admitted: n(0), ticks: n(0)},
  step: {state: {
    level: ite(same(x('kind'), n(0)), minus(x('level'), n(2)), ite(less(x('level'), x('B')), plus(x('level'), n(1)), x('level'))),
    admitted: ite(all(same(x('kind'), n(1)), less(x('level'), x('B'))), plus(x('admitted'), n(1)), x('admitted')),
    ticks: ite(same(x('kind'), n(0)), plus(x('ticks'), n(1)), x('ticks')),
  }},
  assume: atMost(x('kind'), n(1)),
}

export const invariantCases: InvariantCase[] = [
  {what: 'in-flight requests: s <= b + 150', depth: 3, history: {b: 7, t: 63, done: 1}, m: inflight, goal: inflightLoss, goalForm: {coef: {s: 1, b: -1}, d: 150},
    box: {b: 63, s: 255, p: 7, t: 63, done: 1}, small: {b: 7, s: 63, p: 4, t: 7, done: 1},
    coefs: signed([1, 2, 3, 50]), consts: [...range(0, 12), 50, 100, 150, 200], terms: 3},
  {what: 'token bucket: spent <= 10 + 3·ticks', depth: 6, history: {kind: 1, amt: 7}, m: bucket, goal: {name: 'spent <= 10 + 3 ticks', holds: atMost(x('spent'), plus(n(10), times(3, x('ticks'))))}, goalForm: {coef: {spent: 1, ticks: -3}, d: 10},
    box: {tokens: 15, spent: 127, ticks: 31, kind: 1, amt: 15}, small: {tokens: 12, spent: 31, ticks: 7, kind: 1, amt: 5},
    coefs: signed([1, 2, 3]), consts: range(0, 12), terms: 3},
  {what: 'leaky bucket: admitted <= B + 2·ticks', depth: 20, history: {B: 7, kind: 1}, m: leaky, goal: {name: 'admitted <= B + 2 ticks', holds: atMost(x('admitted'), plus(x('B'), times(2, x('ticks'))))}, goalForm: {coef: {admitted: 1, B: -1, ticks: -2}, d: 0},
    box: {B: 31, level: 63, admitted: 127, ticks: 63, kind: 1}, small: {B: 7, level: 15, admitted: 31, ticks: 7, kind: 1},
    coefs: signed([1, 2, 3]), consts: range(0, 6), terms: 3},
]

// Loops. carry: count down b, and when it's out, take one from a and refill b to 3; the rank 4a + b drops each turn.
const carry: Loop = {name: 'carry', params: ['A'], inputs: [], state: {a: x('A'), b: n(0)}, while: any(less(n(0), x('a')), less(n(0), x('b'))),
  body: {a: ite(less(n(0), x('b')), x('a'), minus(x('a'), n(1))), b: ite(less(n(0), x('b')), minus(x('b'), n(1)), n(3))}}
const euclid: Loop = {name: 'gcd by subtraction', params: ['A', 'B'], inputs: [], state: {a: x('A'), b: x('B')}, while: {op: 'not', x: same(x('a'), x('b'))},
  body: {a: ite(less(x('b'), x('a')), minus(x('a'), x('b')), x('a')), b: ite(less(x('a'), x('b')), minus(x('b'), x('a')), x('b'))}, pre: all(atMost(n(1), x('A')), atMost(n(1), x('B')))}
// Two counters racing: x climbs by 2 and y by 1 until x passes y + n; the gap closes by one a turn (rank n + y - x + 1).
const race: Loop = {name: 'race', params: ['n'], inputs: [], state: {x: n(0), y: n(0)}, while: atMost(x('x'), plus(x('y'), x('n'))), body: {x: plus(x('x'), n(2)), y: plus(x('y'), n(1))}}

export const rankCases: RankCase[] = [
  {what: 'carry: while a > 0 or b > 0', l: carry, laws: [{name: 'b <= 3', holds: atMost(x('b'), n(3))}], box: {A: 15, a: 31, b: 7}, small: {A: 7, a: 15, b: 5}, coefs: signed([1, 2, 3, 4, 5]), consts: range(-4, 4), terms: 2},
  {what: 'gcd by subtraction, A, B >= 1', l: euclid, laws: [{name: 'a >= 1', holds: atMost(n(1), x('a'))}, {name: 'b >= 1', holds: atMost(n(1), x('b'))}], box: {A: 15, B: 15, a: 63, b: 63}, small: {A: 7, B: 7, a: 15, b: 15}, coefs: signed([1, 2, 3]), consts: range(-2, 2), terms: 2},
  {what: 'race: x += 2, y += 1 while x <= y + n', l: race, laws: [], box: {n: 63, x: 255, y: 255}, small: {n: 15, x: 63, y: 63}, coefs: signed([1, 2, 3]), consts: range(-3, 3), terms: 3},
]
