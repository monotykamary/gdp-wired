import {expect, test} from 'bun:test'
import {type C, type E, seeded} from '../core/machine.ts'
import {type Goal, check} from './kernel.ts'
import {clock, pairedKeys} from './prove.ts'
import {cdclCandHook, cdclSession, cdclStats, growCdcl} from './cdcl.ts'

const v = (name: string): E => ({op: 'var', name})
const n = (value: number): E => ({op: 'const', value})
const add = (a: E, b: E): E => ({op: 'add', a, b})
const prod = (a: E, b: E): E => ({op: 'prod', a, b})
const tup = (a: E, b: E): E => ({op: 'tup', a, b})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const ite = (c: C, thenE: E, elseE: E): E => ({op: 'if', c, then: thenE, else: elseE})

const withVerify = <T>(f: () => T): {out: T, nodes: number, openTotals: number} => {
  const prevVerify = cdclCandHook.verify, prevOn = cdclCandHook.on
  let nodes = 0, openTotals = 0
  try {
    cdclCandHook.verify = true
    cdclCandHook.on = (_cands, openLen) => { nodes++; openTotals += openLen }
    return {out: f(), nodes, openTotals}
  } finally {
    cdclCandHook.verify = prevVerify
    cdclCandHook.on = prevOn
  }
}

test('incremental openCellsLive matches reference scan on dynamic cell enter/leave/re-enter', () => {
  // Conditional map reads force cells to enter, leave on backtrack, and re-enter in different insertion orders.
  const goal: Goal = {
    name: 'dynamic-cell-reenter',
    hyps: [
      {op: '<=', a: ite({op: '<=', a: v('s'), b: n(0)}, get('M', v('a')), get('M', v('b'))), b: n(1)},
      {op: '<=', a: ite({op: '<=', a: v('t'), b: n(0)}, get('M', v('c')), get('M', v('a'))), b: n(1)},
      {op: '<=', a: ite({op: '<=', a: v('u'), b: n(0)}, get('M', v('d')), get('M', v('b'))), b: n(1)},
      {op: 'or', xs: [{op: '=', a: get('M', v('a')), b: n(0)}, {op: '=', a: get('M', v('d')), b: n(2)}]},
      {op: 'or', xs: [{op: '=', a: get('M', v('b')), b: n(2)}, {op: '=', a: get('M', v('c')), b: n(2)}]},
      {op: '<=', a: get('M', n(0)), b: n(1)},
      {op: '<=', a: get('M', n(1)), b: n(1)},
      {op: '=', a: v('a'), b: v('b')},
      {op: '=', a: v('b'), b: v('c')},
      {op: '=', a: v('c'), b: v('d')},
      {op: '<=', a: n(1), b: get('M', v('a'))},
    ],
  }
  const {out, nodes, openTotals} = withVerify(() => growCdcl(goal, new Map(), {nodes: 0, until: clock() + 2000}))
  expect('tree' in out).toBe(true)
  if ('tree' in out) expect(check(goal, out.tree)).toBe(true)
  expect(nodes).toBeGreaterThan(2)
  expect(openTotals).toBeGreaterThan(0)
})

test('incremental openCellsLive matches reference scan on tuple-keyed maps with shared parts', () => {
  const goal: Goal = {
    name: 'tuple-cells-stream',
    hyps: [
      {op: 'or', xs: [{op: '=', a: get('V', tup(v('n1'), v('v1'))), b: n(0)}, {op: '=', a: get('V', tup(v('n2'), v('v2'))), b: n(0)}]},
      {op: 'or', xs: [{op: '=', a: get('V', tup(v('n1'), v('v2'))), b: n(1)}, {op: '=', a: get('V', tup(v('n2'), v('v1'))), b: n(1)}]},
      {op: 'or', xs: [{op: '=', a: get('V', tup(v('n1'), v('v1'))), b: n(1)}, {op: '=', a: get('V', tup(v('n3'), v('v1'))), b: n(0)}]},
      {op: 'or', xs: [{op: '=', a: get('V', tup(v('n2'), v('v2'))), b: n(1)}, {op: '=', a: get('V', tup(v('n3'), v('v2'))), b: n(0)}]},
      {op: 'or', xs: [{op: '=', a: get('V', tup(v('n3'), v('v1'))), b: n(1)}, {op: '=', a: get('V', tup(v('n3'), v('v2'))), b: n(1)}]},
      {op: 'or', xs: [{op: '=', a: get('V', tup(v('n1'), v('v2'))), b: n(0)}, {op: '=', a: get('V', tup(v('n2'), v('v1'))), b: n(0)}]},
      {op: '<=', a: get('V', tup(v('n3'), tup(v('v1'), v('v2')))), b: n(1)},
      {op: '<=', a: get('V', tup(v('n1'), tup(v('v2'), v('v1')))), b: n(1)},
      {op: '<=', a: v('n1'), b: n(1)},
      {op: '<=', a: v('n2'), b: n(1)},
      {op: '<=', a: v('n3'), b: n(1)},
      {op: '<=', a: v('v1'), b: n(0)},
      {op: '<=', a: v('v2'), b: n(0)},
    ],
  }
  const {out, nodes, openTotals} = withVerify(() => growCdcl(goal, new Map(), {nodes: 0, until: clock() + 2000}))
  expect('tree' in out || out.stuck === 'sat').toBe(true)
  if ('tree' in out) expect(check(goal, out.tree)).toBe(true)
  expect(nodes).toBeGreaterThan(5)
  expect(openTotals).toBeGreaterThan(0)
})

test('incremental openCellsLive handles pairedKeys.skip and multi-run cdclSession toggles', () => {
  const goal: Goal = {
    name: 'monomial-skip-session',
    hyps: [
      {op: '<=', a: get('P', add(prod(v('x'), v('x')), v('y'))), b: n(1)},
      {op: '<=', a: get('P', add(prod(v('z'), v('z')), v('w'))), b: n(1)},
      {op: '<=', a: get('M', v('x')), b: n(1)},
      {op: 'or', xs: [{op: '=', a: get('M', v('y')), b: n(0)}, {op: '=', a: get('M', v('z')), b: n(1)}]},
    ],
  }
  const prevSkip = pairedKeys.skip
  try {
    const sess = cdclSession(goal, new Map(), {model: true})
    pairedKeys.skip = true
    const r1 = withVerify(() => sess.run({nodes: 0, until: clock() + 1000}))
    expect(r1.nodes).toBeGreaterThan(0)
    // Add a new hypothesis and flip pairedKeys.skip between session runs.
    goal.hyps.push({op: '<=', a: get('M', v('w')), b: n(1)}, {op: '=', a: v('x'), b: v('y')})
    pairedKeys.skip = false
    const r2 = withVerify(() => sess.run({nodes: 0, until: clock() + 1000}))
    expect(r2.nodes).toBeGreaterThan(0)
    pairedKeys.skip = true
    const r3 = withVerify(() => sess.run({nodes: 0, until: clock() + 1000}))
    expect(r3.nodes).toBeGreaterThan(0)
  } finally {
    pairedKeys.skip = prevSkip
  }
})

test('incremental openCellsLive matches reference scan on random multi-map goals', () => {
  const rand = seeded(918273)
  const keys = ['a', 'b', 'c', 'd', 'e'] as const
  const maps = ['M', 'N'] as const
  const term = (d: number): E => {
    const r = rand(d <= 0 ? 3 : 7)
    if (r === 0) return v(keys[rand(keys.length)]!)
    if (r === 1) return n(rand(3))
    if (r === 2) return get(maps[rand(maps.length)]!, v(keys[rand(keys.length)]!))
    if (r === 3) return add(term(d - 1), n(rand(2)))
    if (r === 4) return ite(cmp(d - 1), term(d - 1), term(d - 1))
    if (r === 5) return get(maps[rand(maps.length)]!, term(d - 1))
    return get('T', tup(v(keys[rand(3)]!), v(keys[rand(3)]!)))
  }
  const cmp = (d: number): C => {
    const r = rand(5)
    if (r === 3 && d > 0) return {op: rand(2) ? 'and' : 'or', xs: [cmp(d - 1), cmp(d - 1)]}
    if (r === 4 && d > 0) return {op: 'not', x: cmp(d - 1)}
    return {op: (['<', '<=', '='] as const)[rand(3)]!, a: term(d), b: term(d)}
  }
  let proven = 0, sat = 0, totalNodes = 0
  const prevNodes = cdclStats.nodes
  for (let i = 0; i < 40; i++) {
    const goal: Goal = {name: `rand-cells-${i}`, hyps: Array.from({length: 5 + rand(4)}, () => cmp(2))}
    const {out, nodes} = withVerify(() => growCdcl(goal, new Map(), {nodes: 0, until: clock() + 1500}))
    totalNodes += nodes
    if ('tree' in out) { proven++; expect(check(goal, out.tree)).toBe(true) }
    else if (out.stuck === 'sat') sat++
  }
  expect(proven).toBeGreaterThan(0)
  expect(sat).toBeGreaterThan(0)
  expect(totalNodes).toBeGreaterThan(50)
  expect(cdclStats.nodes - prevNodes).toBeGreaterThanOrEqual(totalNodes)
})
