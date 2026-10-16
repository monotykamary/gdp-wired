// Cases for more.ts: loops that need a pair of ranks, and machines whose laws hold at every key of a map.
import {type Law, type Machine, atMost, get, ite, less, max, min, n, plus, x} from '../core/machine.ts'
import {admit, capLaws} from '../core/models.ts'
import type {Loop} from '../kernel/kernel.ts'
import type {Box} from './compile.ts'

const range = (a: number, b: number) => Array.from({length: b - a + 1}, (_, i) => a + i)
const signed = (cs: number[]) => [...cs, ...cs.map(c => -c)]

export type PairCase = {what: string, l: Loop, laws: Law[], box: Box, small: Box, coefs: number[], consts: number[], terms: number}
export type MapCase = {what: string, m: Machine, expect: Law[], box: Box, small: Box, coefs: number[], consts: number[], terms: number}

// kernel/run-more.ts's grid walk: the inner bound m is a param, so no linear rank fits ((m + 1)(n - i) + m - j would).
const grid: Loop = {
  name: 'every cell of an n × m grid', params: ['n', 'm'], inputs: [], state: {i: n(0), j: n(0)},
  while: less(x('i'), x('n')),
  body: {i: ite(less(x('j'), x('m')), x('i'), plus(x('i'), n(1))), j: ite(less(x('j'), x('m')), plus(x('j'), n(1)), n(0))},
}
// A triangle: the inner loop runs up to the outer counter, (n - i, i - j) in order.
const triangle: Loop = {
  name: 'every pair j < i < n', params: ['n'], inputs: [], state: {i: n(0), j: n(0)},
  while: less(x('i'), x('n')),
  body: {i: ite(less(x('j'), x('i')), x('i'), plus(x('i'), n(1))), j: ite(less(x('j'), x('i')), plus(x('j'), n(1)), n(0))},
}
// Retries with backoff inside a budget of rounds: each round takes up to w tries, a param, then the next round.
const rounds: Loop = {
  name: 'rounds of w tries', params: ['R', 'w'], inputs: [], state: {r: n(0), t: n(0)},
  while: less(x('r'), x('R')),
  body: {r: ite(less(x('t'), x('w')), x('r'), plus(x('r'), n(1))), t: ite(less(x('t'), x('w')), plus(x('t'), n(1)), n(0))},
}

export const pairCases: PairCase[] = [
  {what: 'grid walk: while i < n, j up to m', l: grid, laws: [], box: {n: 7, m: 7, i: 15, j: 15}, small: {n: 3, m: 3, i: 7, j: 7}, coefs: signed([1, 2]), consts: range(-2, 2), terms: 2},
  {what: 'triangle: while i < n, j up to i', l: triangle, laws: [], box: {n: 15, i: 31, j: 31}, small: {n: 5, i: 9, j: 9}, coefs: signed([1, 2]), consts: range(-2, 2), terms: 2},
  {what: 'rounds of w tries within R rounds', l: rounds, laws: [], box: {R: 7, w: 7, r: 15, t: 15}, small: {R: 3, w: 3, r: 7, t: 7}, coefs: signed([1, 2]), consts: range(-2, 2), terms: 2},
]

// A leaderboard: each request raises one player's score by up to inc, capped at C, and top follows the highest.
// Needs Score[k] <= top for every k, and top <= C.
const leaderboard: Machine = {
  name: 'leaderboard', params: ['C'], inputs: ['u', 'inc'], state: {top: n(0)}, maps: {Score: 0},
  step: {
    state: {top: max(x('top'), min(plus(get('Score', x('u')), x('inc')), x('C')))},
    maps: {Score: {key: x('u'), value: min(plus(get('Score', x('u')), x('inc')), x('C'))}},
  },
}

export const mapCases: MapCase[] = [
  // Keys within 0..1: k and each written key are equal half of the time. Cells within 0..3, caps within 0..2.
  {what: 'caps rule: the caps, from templates', m: admit(), expect: capLaws,
    box: {d: 2, hr: 2, dm: 2, k: 1, Acct_k: 3, Day_k: 3, Hour_k: 3, Dom_k: 3, acct: 1, day: 1, hour: 1, dom: 1, ok: 1, Acct_w: 3, Day_w: 3, Hour_w: 3, Dom_w: 3},
    small: {d: 1, hr: 1, dm: 1, k: 1, Acct_k: 2, Day_k: 2, Hour_k: 2, Dom_k: 2, acct: 1, day: 1, hour: 1, dom: 1, ok: 1, Acct_w: 2, Day_w: 2, Hour_w: 2, Dom_w: 2},
    coefs: signed([1]), consts: range(0, 2), terms: 2},
  {what: 'leaderboard: every score under top, top under C', m: leaderboard,
    expect: [{name: 'Score[k] <= top', holds: atMost(get('Score', x('k')), x('top')), forall: 'k'}, {name: 'top <= C', holds: atMost(x('top'), x('C'))}],
    box: {C: 7, k: 3, top: 9, Score_k: 9, u: 3, inc: 3, Score_w: 9}, small: {C: 3, k: 1, top: 5, Score_k: 5, u: 1, inc: 2, Score_w: 5},
    coefs: signed([1, 2]), consts: range(-1, 2), terms: 2},
]
