// The counting kind (Count.lean's checkCounted, kernel.ts's twin) and ghost maps (GhostMap.lean's smghostOk, kernel.ts's
// ghostedOk): the hand-built examples accepted, each guard refusing what only it refuses (a certificate whose tree the
// rest of the check accepts: the goal a guard's absence would check, grown by the search), and a soundness fuzz: every
// counted goal the kernel accepts has no model where each count is its sum, by brute force.
import {describe, expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, any, atMost, get, ite, less, n, not, plus, same, times, x} from '../core/machine.ts'
import {type Count, type CountedGoal, type CountInst, type Ghosted, type Goal, type Tree, check, checkCounted, checkGhostedLaws, countedGoal, countHyps, ghostedMachine, ghostedOk} from './kernel.ts'
import {clock, grow, proveLaws} from './prove.ts'
import {byzantineStep, countTree, grants, majorityStep, thresholdStep} from '../lean-kernel/count-examples.ts'

const scale = Number(process.env.FUZZ_SCALE ?? 1)
const treeOf = (goal: Goal | undefined, ms = 20_000): Tree | undefined => {
  if (!goal) return undefined
  const out = grow(goal, new Map(), {nodes: 0, until: clock() + ms})
  return 'tree' in out ? out.tree : undefined
}

// --- the meaning, by brute force: naturals, ∸ truncating, each count its sum ----------------------------------------------
type Env = Record<string, number>
type Maps = Record<string, number[]>
const ev = (e: E, env: Env, maps: Maps): number => {
  switch (e.op) {
    case 'var': return env[e.name] ?? 0
    case 'const': return e.value
    case 'add': return ev(e.a, env, maps) + ev(e.b, env, maps)
    case 'sub': return Math.max(0, ev(e.a, env, maps) - ev(e.b, env, maps))
    case 'mul': return e.k * ev(e.a, env, maps)
    case 'prod': return ev(e.a, env, maps) * ev(e.b, env, maps)
    case 'min': return Math.min(ev(e.a, env, maps), ev(e.b, env, maps))
    case 'max': return Math.max(ev(e.a, env, maps), ev(e.b, env, maps))
    case 'if': return holds(e.c, env, maps) ? ev(e.then, env, maps) : ev(e.else, env, maps)
    case 'get': return maps[e.map]?.[ev(e.key, env, maps)] ?? 0
  }
}
const holds = (c: C, env: Env, maps: Maps): boolean => {
  switch (c.op) {
    case '<': return ev(c.a, env, maps) < ev(c.b, env, maps)
    case '<=': return ev(c.a, env, maps) <= ev(c.b, env, maps)
    case '=': return ev(c.a, env, maps) === ev(c.b, env, maps)
    case 'not': return !holds(c.x, env, maps)
    case 'and': return c.xs.every(y => holds(y, env, maps))
    case 'or': return c.xs.some(y => holds(y, env, maps))
    default: throw new Error(`no ${c.op} here`)
  }
}
const sumOf = (cn: Count, env: Env, maps: Maps): number => {
  let s = 0
  for (let k = 0; k < ev(cn.below, env, maps); k++) s += ev(cn.body, {...env, [cn.key]: k}, maps)
  return s
}
// A model of a counted goal: an environment and maps where each count is its sum and every hypothesis holds.
function hasModel(g: CountedGoal, envs: Env[], mapss: Maps[]): boolean {
  for (const env0 of envs) for (const maps of mapss) {
    const env = {...env0}
    for (const cn of g.counts) env[cn.v] = sumOf(cn, env, maps)
    if (g.hyps.every(h => holds(h, env, maps))) return true
  }
  return false
}
const range = (k: number) => Array.from({length: k}, (_, i) => i)
const product = <T>(xs: T[][]): T[][] => xs.reduce<T[][]>((acc, ys) => acc.flatMap(a => ys.map(y => [...a, y])), [[]])

// --- counts ----------------------------------------------------------------------------------------------------------------

describe('counts', () => {
  const examples = [{name: 'majority', ...majorityStep()}, {name: 'threshold', ...thresholdStep()}, {name: 'byzantine', ...byzantineStep()}]
  const trees = new Map(examples.map(ex => [ex.name, countTree(ex.g, ex.insts)]))
  const {g, insts} = examples[0]!, tree = trees.get('majority')!

  for (const ex of examples) test(`${ex.name}: the certificate checks`, () => {
    const t = trees.get(ex.name)
    expect(t).toBeDefined()
    expect(checkCounted(ex.g, {insts: ex.insts, tree: t!})).toBe(true)
  })

  test('the examples have no model where each count is its sum (small instances), and do without the counts', () => {
    // majority: N ≤ 3 nodes, values a, b, v ≤ 1, any votes (0 none, i + 1 for i) and decisions
    const votes = (k: number) => product(range(k).map(() => range(3)))
    const mapss = [0, 1, 2, 3].flatMap(N => votes(N).flatMap(vote => product([range(2), range(2)]).map(d => ({vote, decided: d}))))
    const envs = product([range(4), range(2), range(2), range(2)]).map(([N, a, b, v]) => ({N: N!, a: a!, b: b!, v: v!}))
    expect(hasModel(g, envs, mapss)).toBe(false)
    // the counts free (any naturals up to 4): a model exists, so the lemma is what refutes the step
    const free: CountedGoal = {...g, counts: []}
    const envsFree = envs.flatMap(e => product([range(5), range(5), range(5)]).map(([cA, cB, cV]) => ({...e, cA: cA!, cB: cB!, cV: cV!})))
    expect(hasModel(free, envsFree, [{vote: [], decided: [1, 0]}, {vote: [], decided: [0, 1]}])).toBe(true)
  })

  test('the tree refutes the goal only with the instances\' hypotheses', () => {
    expect(check({name: g.name, hyps: g.hyps}, tree)).toBe(false)
    expect(treeOf({name: g.name, hyps: g.hyps}, 3000)).toBeUndefined()
  })

  test('a tree for another goal is refused', () => {
    expect(checkCounted(g, {insts, tree: trees.get('threshold')!})).toBe(false)
  })

  // Each guard refuses a certificate whose tree the rest of the check accepts.
  const refusedByGuard = (what: string, g2: CountedGoal, insts2: CountInst[], goal2 = countedGoal(g2, insts2)) => test(`refused: ${what}`, () => {
    const t = treeOf(goal2)
    expect(t).toBeDefined()
    expect(check(goal2!, t!)).toBe(true)
    expect(checkCounted(g2, {insts: insts2, tree: t!})).toBe(false)
  })
  refusedByGuard('two instances with one witness', g, insts.map(i => ({...i, wit: 'w'})))
  refusedByGuard('a hypothesis reads a witness', {...g, hyps: [...g.hyps, atMost(x('w1'), x('w1'))]}, insts)
  refusedByGuard('a witness is a count\'s variable', g, insts.map((i, j) => (j === 0 ? {...i, wit: 'cB'} : i)))
  refusedByGuard('a count\'s bound reads a witness', {...g, counts: [...g.counts, {v: 'cZ', key: 'n', below: plus(x('N'), times(0, x('w1'))), body: n(1)}]}, insts)
  refusedByGuard('a count\'s body reads a witness', {...g, counts: [...g.counts, {v: 'cZ', key: 'n', below: x('N'), body: ite(same(get('vote', x('n')), x('w1')), n(1), n(0))}]}, insts)
  refusedByGuard('an instance\'s bound reads a witness', g, [...insts, {wit: 'w3', below: plus(x('N'), times(0, x('w1'))), terms: [], unit: 0}])
  refusedByGuard('a unit coefficient not an integer', g, [...insts, {wit: 'w3', below: x('N'), terms: [], unit: 0.5}])
  refusedByGuard('a count coefficient not an integer', g, [...insts, {wit: 'w3', below: x('N'), terms: [[1, 'cA'], [0.5, 'cB']], unit: 0}])
  // A bound unlike the count's: kernel.ts builds no hypothesis; the goal checked had it been built with the instance's
  // bound (its hypothesis reads the instance's bound only) is refuted.
  {
    const bad = insts.map((i, j) => (j === 0 ? {...i, below: plus(x('N'), n(0))} : i))
    const patched = g.counts.map(cn => ({...cn, below: plus(x('N'), n(0))}))
    refusedByGuard('an instance\'s bound unlike its counts\' (by structure)', g, bad,
      {name: g.name, hyps: [...g.hyps, ...countHyps(patched, bad.slice(0, 1))!, ...countHyps(g.counts, bad.slice(1))!]})
  }
  test('an instance naming no count is refused', () => {
    expect(checkCounted(g, {insts: [...insts, {wit: 'w3', below: x('N'), terms: [[1, 'cQ']], unit: 0}], tree})).toBe(false)
  })

  // Bounds compared by structure: the order of a term's fields doesn't matter, its constants do. A count of N + 2 keys,
  // all of them: it is N + 2, so cA ≤ N + 1 would be false; read with the bound N + 1, the instance says just that.
  const small = (below: E): CountedGoal => ({name: 'cA = N + 2', hyps: [same(x('cA'), plus(x('N'), n(2)))], counts: [{v: 'cA', key: 'n', below, body: n(1)}]})
  test('bounds alike by structure, fields in any order', () => {
    const g2: CountedGoal = {name: 'N + 2 ≤ cA', hyps: [atMost(plus(x('N'), n(2)), x('cA'))], counts: [{v: 'cA', key: 'n', below: plus(x('N'), n(1)), body: n(1)}]}
    const reordered = JSON.parse('{"b": {"value": 1, "op": "const"}, "a": {"name": "N", "op": "var"}, "op": "add"}') as E
    const insts2: CountInst[] = [{wit: 'w', below: reordered, terms: [[1, 'cA']], unit: -1}]
    const t = treeOf(countedGoal(g2, insts2))
    expect(t).toBeDefined()
    expect(checkCounted(g2, {insts: insts2, tree: t!})).toBe(true)
  })
  refusedByGuard('a bound unlike the count\'s by a constant (cA = N + 2 refuted, unsoundly)', small(plus(x('N'), n(2))),
    [{wit: 'w', below: plus(x('N'), n(1)), terms: [[1, 'cA']], unit: -1}],
    {name: 'cA = N + 2', hyps: [same(x('cA'), plus(x('N'), n(2))), ...countHyps([{v: 'cA', key: 'n', below: plus(x('N'), n(1)), body: n(1)}], [{wit: 'w', below: plus(x('N'), n(1)), terms: [[1, 'cA']], unit: -1}])!]})
  test('that goal has a model: cA = N + 2 is its count', () => {
    expect(hasModel(small(plus(x('N'), n(2))), range(4).map(N => ({N})), [{}])).toBe(true)
  })

  // Soundness fuzz: random hypotheses over counts of three sets of the nodes below N (votes for x, for y, any vote) and
  // N, random instances; every goal the kernel accepts has no model (N ≤ 3, x, y ≤ 2, any votes ≤ 2).
  test('fuzz: every accepted counted goal has no model where each count is its sum', () => {
    let seed = Number(process.env.FUZZ_SEED ?? 7)
    const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
    const counts: Count[] = [
      {v: 'cX', key: 'n', below: x('N'), body: ite(same(get('vote', x('n')), plus(x('x'), n(1))), n(1), n(0))},
      {v: 'cY', key: 'n', below: x('N'), body: ite(same(get('vote', x('n')), plus(x('y'), n(1))), n(1), n(0))},
      {v: 'cV', key: 'n', below: x('N'), body: ite(less(n(0), get('vote', x('n'))), n(1), n(0))},
    ]
    const atoms = ['cX', 'cY', 'cV', 'N', 'x', 'y']
    const lin = (): E => { let e: E = n(rand(3)); for (const a of atoms) if (rand(3) === 0) e = plus(e, times(1 + rand(2), x(a))); return e }
    const cmp = (): C => { const r = rand(4); const c: C = {op: (['<', '<=', '='] as const)[rand(3)]!, a: lin(), b: lin()}; return r === 0 ? not(c) : r === 1 ? any(c, {op: '=', a: x('x'), b: x('y')}) : c }
    const envs = product([range(4), range(3), range(3)]).map(([N, xx, yy]) => ({N: N!, x: xx!, y: yy!}))
    const mapss = [0, 1, 2, 3].flatMap(k => product(range(k).map(() => range(3))).map(vote => ({vote})))
    let accepted = 0, withInstances = 0
    const tries = Math.round(300 * scale)
    for (let i = 0; i < tries; i++) {
      const g2: CountedGoal = {name: `fuzz ${i}`, hyps: Array.from({length: 1 + rand(3)}, cmp), counts}
      const insts2: CountInst[] = Array.from({length: rand(3)}, (_, j) => ({wit: `w${j}`, below: x('N'), unit: rand(5) - 2,
        terms: counts.filter(() => rand(2) === 0).map(cn => [rand(5) - 2, cn.v] as [number, string])}))
      const t = treeOf(countedGoal(g2, insts2), 400)
      if (!t || !checkCounted(g2, {insts: insts2, tree: t})) continue
      accepted++
      // (accepted without the instances' hypotheses: the counts read as free naturals)
      if (!check({name: g2.name, hyps: g2.hyps}, t)) withInstances++
      expect(hasModel(g2, envs, mapss)).toBe(false)
    }
    console.log(`fuzz: ${tries} goals, ${accepted} accepted, ${withInstances} of them only with the instances' hypotheses`)
    expect(withInstances).toBeGreaterThan(Math.min(5, tries / 20))
  })
})

// --- ghost maps ------------------------------------------------------------------------------------------------------------

describe('ghost maps', () => {
  const {g, laws} = grants()
  const proof = proveLaws(ghostedMachine(g), laws).proof

  test('grants: the ghosted machine\'s laws check, and the ghosts are apart', () => {
    expect(proof).toBeDefined()
    expect(ghostedOk(g)).toBe(true)
    expect(checkGhostedLaws(g, laws, proof!)).toBe(true)
  })

  test('grants: on random runs of the original, every grant has some valid ticket (the law read ∀∃)', () => {
    let seed = 11
    const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
    for (let run = 0; run < 50; run++) {
      const T = 1 + rand(3), valid = new Map<number, number>(), granted = new Map<number, number>()
      for (let s = 0; s < 20; s++) {
        const op = rand(2), k = rand(4), t = rand(4)
        if (op === 0 && t < T) valid.set(t, 1)
        if (op === 1 && valid.get(t) === 1 && t < T) granted.set(k, 1)
        for (const v of granted.values()) if (v === 1) expect(range(T).some(t2 => valid.get(t2) === 1)).toBe(true)
      }
    }
  })

  // Each guard of ghostedOk refuses a ghosted machine only it refuses.
  const W2: Ghosted['maps'] = {W2: {start: 0, write: {key: x('k'), value: n(0)}}}
  const gv: Ghosted['vars'] = {gv: {start: n(0), step: n(1)}, hv: {start: n(0), step: n(0)}}
  const quant: Machine = {...g.orig, step: {...g.orig.step, flags: {q: {op: 'all', key: 'kk', c: atMost(get('valid', x('kk')), n(1))}}}}
  const cases: [string, Ghosted][] = [
    ['the original keeps a history', {...g, orig: {...g.orig, history: {keep: atMost(n(0), n(0)), record: [], sums: {}, queries: {}}} as unknown as Machine}],
    ['the original keeps sums', {...g, orig: {...g.orig, sums: {s: {key: 'j', term: get('granted', x('j'))}}}}],
    ['a ghost variable is one of the original\'s (an input)', {...g, vars: {zz: {start: n(0), step: n(0)}, k: {start: n(0), step: n(0)}}}],
    ['a ghost variable is a quantified flag\'s witness', {...g, orig: quant, vars: {zz: {start: n(0), step: n(0)}, 'w?q': {start: n(0), step: n(0)}}}],
    ['a ghost map is one of the original\'s', {...g, maps: {...g.maps, valid: {start: 0, write: {key: x('k'), value: n(0)}}}}],
    ['the original\'s assumption reads a ghost variable', {...g, vars: gv, orig: {...g.orig, assume: atMost(x('gv'), n(5))}}],
    ['the original\'s write reads a ghost map', {...g, maps: {...g.maps, ...W2}, orig: {...g.orig, step: {...g.orig.step, maps: {...g.orig.step.maps,
      granted: {key: x('k'), value: ite(same(get('W', x('k')), n(7)), n(0), get('granted', x('k')))}}}}}],
  ]
  for (const [what, bad] of cases) test(`refused: ${what}`, () => {
    expect(ghostedOk(bad)).toBe(false)
  })
  test('refused, with the laws checking: the original\'s assumption reads a ghost map', () => {
    const bad: Ghosted = {...g, maps: {...g.maps, ...W2}, orig: {...g.orig, assume: same(get('W', x('k')), n(0))}}
    const p = proveLaws(ghostedMachine(bad), laws).proof
    expect(p).toBeDefined()
    expect(checkGhostedLaws(bad, laws, p!)).toBe(false)
  })
})
