import {expect, test} from 'bun:test'
import {type C, type E, any, atMost, get, ite, less, min, minus, n, not, plus, same, walkOnce, x} from '../core/machine.ts'
import {check, checkLaws, leafConstraints, obligations} from './kernel.ts'
import {Reader} from './reader.ts'
import {dagInterner, findSelector, preSplitBySelector, preSplitStats, specializeGoal} from './dag-split.ts'
import {brokenOf, clock, grow, growWide, openAt, proveLaws, treeReuseStats, withTrees} from './prove.ts'
import {nat, oneOf, proveRule, rule, when} from '../core/dsl.ts'

function sharedDagExpr(depth: number, leaf: E): E {
  let e: E = leaf
  for (let i = 0; i < depth; i++) {
    e = ite(atMost(n(0), x('p')), plus(e, n(0)), e)
  }
  return e
}

function sharedOpenCond(depth: number): C {
  let e: E = x('a')
  for (let i = 0; i < depth; i++) {
    e = ite(atMost(x(`c${i}`), n(10)), plus(e, e), e)
  }
  return atMost(n(0), e)
}

test('dagInterner assigns identical IDs to structurally equal shared DAGs without exponential unrolling', () => {
  const dag = dagInterner()
  const e1 = sharedDagExpr(26, x('k'))
  const e2 = sharedDagExpr(26, x('k'))
  const e3 = sharedDagExpr(26, x('m'))

  const t0 = performance.now()
  const id1 = dag.id(e1)
  const id2 = dag.id(e2)
  const id3 = dag.id(e3)
  const ms = performance.now() - t0

  expect(id1).toBeDefined()
  expect(id2).toBe(id1)
  expect(id3).not.toBe(id1)
  expect(ms).toBeLessThan(1000)

  const cyc: Record<string, unknown> = {op: 'cyc'}
  cyc.self = cyc
  expect(dag.id(cyc)).toBeUndefined()
})

test('withTrees caches depth-26 heavily shared DAG goals without JSON.stringify blowup', () => {
  const makeGoal = (name: string) => {
    const deep = sharedDagExpr(26, x('v'))
    return {
      name,
      hyps: [
        atMost(n(0), x('p')),
        atMost(deep, x('v')),
        atMost(plus(x('v'), n(1)), deep),
      ],
    }
  }
  const g1 = makeGoal('deep-1')
  const g2 = makeGoal('deep-2')
  const beforeHits = treeReuseStats.hits

  const t0 = performance.now()
  withTrees(() => {
    const out1 = grow(g1, new Map(), {nodes: 0, until: clock() + 5000})
    const out2 = grow(g2, new Map(), {nodes: 0, until: clock() + 5000})
    expect('tree' in out1 && 'tree' in out2).toBe(true)
    if ('tree' in out1 && 'tree' in out2) {
      expect(out2.tree).toBe(out1.tree)
      expect(check(g1, out1.tree)).toBe(true)
      expect(check(g2, out2.tree)).toBe(true)
    }
  })
  expect(performance.now() - t0).toBeLessThan(2000)
  expect(treeReuseStats.hits - beforeHits).toBe(1)
})

test('growWide cellsIn handles depth-24 heavily shared map keys without blowup', () => {
  const deepKey = sharedDagExpr(24, x('k'))
  const goal = {
    name: 'wide-shared-key',
    hyps: [
      atMost(n(0), x('p')),
      atMost(n(0), get('M', deepKey)),
      atMost(get('M', deepKey), n(5)),
      not(atMost(get('M', deepKey), n(5))),
    ],
  }
  const t0 = performance.now()
  const out = growWide(goal, {nodes: 0, until: clock() + 5000})
  const ms = performance.now() - t0
  expect(out && 'tree' in out).toBe(true)
  if (out && 'tree' in out) {
    expect(check(goal, out.tree)).toBe(true)
  }
  expect(ms).toBeLessThan(2000)
})

test('openAt and Reader.openList stay O(distinct DAG nodes) on deeply shared open conditions', () => {
  const deep = sharedOpenCond(22)
  const goal = {name: 'deep-open', hyps: [deep]}
  const p = new Map()
  const rows = leafConstraints(goal, p)

  const t0 = performance.now()
  const open = openAt(goal, p, rows)
  const openMs = performance.now() - t0

  const trail = {
    get: () => undefined,
    stamp: () => 0,
    size: () => 0,
    lin: () => { throw new Error('empty') },
  }
  const reader = new Reader(goal, trail)
  reader.begin()
  reader.sync(0)
  const t1 = performance.now()
  const rOpen = reader.openList(0)
  const readerMs = performance.now() - t1

  expect(open.length).toBeGreaterThan(0)
  expect(open.length).toBeLessThan(200)
  expect(rOpen.length).toBeGreaterThan(0)
  expect(rOpen.length).toBeLessThan(200)
  expect(openMs).toBeLessThan(1000)
  expect(readerMs).toBeLessThan(1000)
})

function buildActionStepGoal(opts: {actions: number, branchesPerAction: number, buggyAction?: number}) {
  const {actions, branchesPerAction, buggyAction} = opts
  // Build a realistic multi-action @step transition where `action in 0..actions-1`
  // dispatches to distinct heavy update expressions (including rewritten min/sub/if
  // choice terms inside open branches so widenToWhole term-column remapping is exercised).
  const actionExpr = (k: number): E => {
    let e: E = x('bal')
    for (let i = 0; i < branchesPerAction; i++) {
      const cond = atMost(x(`flag_${k}_${i}`), n(0))
      const inner = i % 3 === 0
        ? min(x('bal'), plus(x(`cap_${k}_${i}`), n(10)))
        : i % 3 === 1
          ? minus(x('bal'), x(`dec_${k}_${i}`))
          : ite(atMost(x(`sub_${k}_${i}`), n(5)), x('bal'), plus(n(0), x('bal')))
      e = ite(cond, inner, e)
    }
    if (buggyAction === k) {
      return plus(e, n(100))
    }
    return min(e, x('limit'))
  }

  let nextBal: E = x('bal')
  for (let k = actions - 1; k >= 0; k--) {
    nextBal = ite(same(x('action'), n(k)), actionExpr(k), nextBal)
  }

  const hyps: C[] = [
    atMost(n(0), x('action')),
    less(x('action'), n(actions)),
    atMost(n(0), x('bal')),
    atMost(x('bal'), x('limit')),
    atMost(n(0), x('limit')),
    // Concluded violation: nextBal > limit (should be refuted unless buggyAction fires)
    not(atMost(nextBal, x('limit'))),
  ]
  return {name: `synthetic @step (bug=${buggyAction ?? 'none'})`, hyps}
}

test('preSplitBySelector proves multi-action goal with rewritten choice terms and checks in unmodified kernel', () => {
  const goal = buildActionStepGoal({actions: 6, branchesPerAction: 6})
  const beforeProven = preSplitStats.proven
  const out = preSplitBySelector(goal, {
    origNodes: 5000,
    budget: {nodes: 0, until: clock() + 5000},
    clock,
    withinDeadline: u => u,
    pastWall: () => false,
    late: () => false,
    searchWork: () => 0,
    searchWorkCap: () => Infinity,
    withSearchWork: (_cap, f) => f(),
    growSub: (g, until) => grow(g, new Map(), {nodes: 0, until}),
    growFallback: (g, p) => { const o = grow(g, p, {nodes: 0, until: clock() + 5000}); return 'tree' in o ? o.tree : undefined },
    brokenOf,
  })
  expect(out && 'tree' in out).toBe(true)
  if (out && 'tree' in out) {
    expect(check(goal, out.tree)).toBe(true)
  }
  expect(preSplitStats.proven).toBe(beforeProven + 1)
})

test('preSplitBySelector finds verified witness on buggy action', () => {
  const goal = buildActionStepGoal({actions: 6, branchesPerAction: 5, buggyAction: 4})
  const beforeSat = preSplitStats.sat
  const out = preSplitBySelector(goal, {
    origNodes: 5000,
    budget: {nodes: 0, until: clock() + 5000},
    clock,
    withinDeadline: u => u,
    pastWall: () => false,
    late: () => false,
    searchWork: () => 0,
    searchWorkCap: () => Infinity,
    withSearchWork: (_cap, f) => f(),
    growSub: (g, until) => grow(g, new Map(), {nodes: 0, until}),
    growFallback: (g, p) => { const o = grow(g, p, {nodes: 0, until: clock() + 5000}); return 'tree' in o ? o.tree : undefined },
    brokenOf,
  })
  expect(out && 'stuck' in out && out.stuck === 'sat').toBe(true)
  if (out && 'stuck' in out && out.witness) {
    expect(out.witness.action).toBe(4)
    expect(brokenOf(goal)(out.witness)).toEqual([])
  }
  expect(preSplitStats.sat).toBe(beforeSat + 1)
})

test('findSelector skips bounded variables that do not shrink the DAG', () => {
  const fillers: C[] = []
  for (let i = 0; i < 100; i++) fillers.push(atMost(x(`u${i}`), x(`v${i}`)))
  const goal = {
    name: 'non-selector',
    hyps: [
      atMost(n(0), x('mode')),
      atMost(x('mode'), n(3)),
      any(same(x('mode'), n(0)), same(x('mode'), n(1)), same(x('mode'), n(2)), same(x('mode'), n(3))),
      ...fillers,
      not(atMost(n(0), x('u0'))),
    ],
  }
  let origNodes = 0
  walkOnce(goal.hyps, () => { origNodes++ })
  expect(findSelector(goal, origNodes)).toBeUndefined()
  const spec = specializeGoal(goal, new Map(), 'mode', 0)
  expect(spec.goal.hyps[0]).toEqual(same(x('mode'), n(0)))

  // A 0..1 boolean flag that leaves >=95% of the DAG intact must never pass the
  // selector shrink check (mean * 2 <= 2.2 alone would trivially pass any boolean).
  const boolGoal = {
    name: 'non-shrinking-bool-flag',
    hyps: [
      atMost(n(0), x('?all$1')),
      atMost(x('?all$1'), n(1)),
      any(same(x('?all$1'), n(0)), same(x('?all$1'), n(1))),
      ...fillers,
      not(atMost(n(0), x('u0'))),
    ],
  }
  let boolNodes = 0
  walkOnce(boolGoal.hyps, () => { boolNodes++ })
  expect(findSelector(boolGoal, boolNodes)).toBeUndefined()
})

test('proveRule with pre-split on large oneOf multi-action rule produces kernel-checked proof', () => {
  const r = rule('multi-action')
    .state({bal: 0, limit: 10, a0: 0, a1: 0, a2: 0, a3: 0, a4: 0, a5: 0})
    .inputs({
      action: oneOf('k0', 'k1', 'k2', 'k3', 'k4', 'k5'),
      amt: nat,
      d0: nat, d1: nat, d2: nat, d3: nat,
    })
    .step(({bal, limit, a0, a1, a2, a3, a4, a5, action, amt, d0, d1, d2, d3}) => {
      const work = (base: number) => {
        let cur = bal
        for (let i = 0; i < 3; i++) {
          const cond = d0.atMost(i + base).and(d1.atMost(i + 2), d2.atMost(i + 3), d3.atMost(i + 4))
          const next = cur.plus(amt)
          cur = when(cond, when(next.atMost(limit), next, limit), cur)
        }
        return cur
      }
      return {
        bal: action.match({
          k0: () => work(0),
          k1: () => work(1),
          k2: () => work(2),
          k3: () => work(3),
          k4: () => work(4),
          k5: () => work(5),
        }),
        a0: when(action.is('k0'), a0.plus(1), a0),
        a1: when(action.is('k1'), a1.plus(1), a1),
        a2: when(action.is('k2'), a2.plus(1), a2),
        a3: when(action.is('k3'), a3.plus(1), a3),
        a4: when(action.is('k4'), a4.plus(1), a4),
        a5: when(action.is('k5'), a5.plus(1), a5),
      }
    })
  const laws = [
    r.law('bal within limit', ({bal, limit}) => bal.atMost(limit)),
  ]
  const v = proveRule(r, laws, {search: false})
  expect(v.proven).toBe(true)
  expect(v.checked).toBe(true)
  const p = proveLaws(r.machine, laws)
  expect(p.proven && p.checked && p.proof !== undefined).toBe(true)
  if (p.proof) expect(checkLaws(r.machine, laws, p.proof)).toBe(true)
  const gs = obligations(r.machine, laws)
  expect(gs.length).toBeGreaterThanOrEqual(2)
})
