// Beyond step machines, through the same kernel: loops that halt (a rank found from templates), laws of every tree (a
// fold's structural induction), and integer systems that elimination alone can't decide.
import {type C, type E, type Law, type Machine, all, atMost, ite, less, min, max, minus, n, not, plus, prod, same, times, x} from '../core/machine.ts'
import {type Goal, type Fold, type Loop, check, foldObligations, loopObligations, obligations} from './kernel.ts'
import {concretize, countLeaves, grow} from './prove.ts'

function decideAll(goals: Goal[]): {ok: boolean, leaves: number, stuck?: string} {
  let leaves = 0
  for (const g of goals) {
    const out = grow(g)
    if (!('tree' in out)) return {ok: false, leaves, stuck: `${g.name}: ${out.stuck} ${out.witness ? JSON.stringify(Object.fromEntries(Object.entries(out.witness).filter(([, v]) => v !== 0))) : ''}`}
    if (!check(g, out.tree)) return {ok: false, leaves, stuck: `${g.name}: kernel REJECTS`}
    leaves += countLeaves(out.tree)
  }
  return {ok: true, leaves}
}

// Ranks to try, smallest first: a state variable, a param minus a state variable, a sum of two state variables.
function ranks(l: Loop): {text: string, e: E}[] {
  const st = Object.keys(l.state)
  return [
    ...st.map(u => ({text: u, e: x(u)})),
    ...l.params.flatMap(y => st.map(u => ({text: `${y} ∸ ${u}`, e: minus(x(y), x(u))}))),
    ...st.flatMap((u, i) => st.slice(i + 1).map(w => ({text: `${u} + ${w}`, e: plus(x(u), x(w))}))),
  ]
}
function halts(what: string, l: Loop, laws: Law[]) {
  const t0 = performance.now()
  for (const r of ranks(l)) {
    const out = decideAll(loopObligations(l, laws, r.e))
    if (out.ok) return console.log(`  ${what.padEnd(46)} HALTS    rank ${r.text}, ${out.leaves} leaves, kernel accepts  (${Math.round(performance.now() - t0)} ms)`)
  }
  const inv = decideAll(loopObligations(l, laws, n(0)).filter(g => g.name !== 'rank drops'))
  console.log(`  ${what.padEnd(46)} NO RANK  among ${ranks(l).length} templates${inv.ok ? '' : `; invariant: ${inv.stuck}`}  (${Math.round(performance.now() - t0)} ms)`)
}

console.log('Termination')
const euclid: Loop = {
  name: 'gcd by subtraction', params: ['A', 'B'], inputs: [], state: {a: x('A'), b: x('B')},
  while: not(same(x('a'), x('b'))),
  body: {a: ite(less(x('b'), x('a')), minus(x('a'), x('b')), x('a')), b: ite(less(x('a'), x('b')), minus(x('b'), x('a')), x('b'))},
  pre: all(atMost(n(1), x('A')), atMost(n(1), x('B'))),
}
const positive: Law[] = [{name: 'a >= 1', holds: atMost(n(1), x('a'))}, {name: 'b >= 1', holds: atMost(n(1), x('b'))}]
halts('gcd by subtraction, A, B >= 1', euclid, positive)
halts('gcd by subtraction, no invariant', euclid, [])
const pages = (minPage: number): Loop => ({
  name: 'pagination', params: ['total'], inputs: ['page'], state: {cur: n(0)},
  while: less(x('cur'), x('total')), body: {cur: plus(x('cur'), min(x('page'), minus(x('total'), x('cur'))))},
  assume: atMost(n(minPage), x('page')),
})
halts('pagination, the server sends pages of >= 1', pages(1), [])
halts('pagination, a page may be empty', pages(0), [])
const retry = (floor: E): Loop => ({
  name: 'retry', params: ['budget'], inputs: ['wait'], state: {spent: n(0), tries: n(0)},
  while: less(x('spent'), x('budget')), body: {spent: plus(x('spent'), max(floor, x('wait'))), tries: plus(x('tries'), n(1))},
})
halts('retry until the budget, each try costs >= 1', retry(n(1)), [])
halts('retry until the budget, a try may cost 0', retry(n(0)), [])

// A rank that reads the turn's input is refused: here it drops each turn, yet w = x + 1 every turn runs forever.
const forever: Loop = {name: 'forever', params: [], inputs: ['w'], state: {x: n(0)}, while: less(x('x'), x('w')), body: {x: plus(x('x'), n(1))}}
try { loopObligations(forever, [], minus(x('w'), x('x'))); console.log('  rank w ∸ x reading the input w                  ACCEPTED (unsound)') }
catch { console.log(`  ${'while x < w: x + 1, rank w ∸ x (w an input)'.padEnd(46)} REFUSED  a rank may not read the turn's input`) }

console.log('Every tree (structural induction)')
const tree = (what: string, f: Fold, laws: Law[]) => {
  const t0 = performance.now()
  const out = decideAll(foldObligations(f, laws))
  console.log(`  ${what.padEnd(46)} ${out.ok ? `PROVEN   ${out.leaves} leaves, kernel accepts` : `STUCK    ${out.stuck}`}  (${Math.round(performance.now() - t0)} ms)`)
}
const shape: Fold = {
  name: 'shape', params: [], inputs: [], leaf: {leaves: n(1), nodes: n(0), height: n(0)},
  node: {leaves: plus(x('l_leaves'), x('r_leaves')), nodes: plus(plus(x('l_nodes'), x('r_nodes')), n(1)), height: plus(max(x('l_height'), x('r_height')), n(1))},
}
tree('leaves = nodes + 1', shape, [{name: 'leaves = nodes + 1', holds: same(x('leaves'), plus(x('nodes'), n(1)))}])
tree('height <= nodes', shape, [{name: 'height <= nodes', holds: atMost(x('height'), x('nodes'))}])
tree('height < leaves', shape, [{name: 'height < leaves', holds: less(x('height'), x('leaves'))}])
tree('leaves = nodes (false)', shape, [{name: 'leaves = nodes', holds: same(x('leaves'), x('nodes'))}])
const rollup = (cap: number): Fold => ({
  name: 'spend roll-up', params: [], inputs: ['c'], leaf: {spend: min(x('c'), n(cap)), count: n(1)},
  node: {spend: plus(x('l_spend'), x('r_spend')), count: plus(x('l_count'), x('r_count'))},
})
tree('spend roll-up: spend <= 50 × requests', rollup(50), [{name: 'spend <= 50 count', holds: atMost(x('spend'), times(50, x('count')))}])
tree('spend roll-up: spend <= 49 × requests (false)', rollup(50), [{name: 'spend <= 49 count', holds: atMost(x('spend'), times(49, x('count')))}])

console.log('Products (monomials as atoms)')
const rollupM: Fold = {name: 'spend roll-up', params: ['m'], inputs: ['c'], leaf: {spend: min(x('c'), x('m')), count: n(1)}, node: {spend: plus(x('l_spend'), x('r_spend')), count: plus(x('l_count'), x('r_count'))}}
tree('roll-up, cap m a param: spend <= m × requests', rollupM, [{name: 'spend <= m count', holds: atMost(x('spend'), prod(x('m'), x('count')))}])
const counted: Machine = {name: 'loss, counted', params: ['m'], inputs: ['c'], state: {s: n(0), r: n(0)}, step: {state: {s: plus(x('s'), min(x('c'), x('m'))), r: plus(x('r'), n(1))}}}
const lin = decideAll(obligations(counted, [{name: 's <= m × requests', holds: atMost(x('s'), prod(x('m'), x('r')))}]))
console.log(`  ${'grind\'s lemma as a machine: s <= m × requests'.padEnd(46)} ${lin.ok ? `PROVEN   ${lin.leaves} leaves, kernel accepts` : `STUCK    ${lin.stuck}`}`)
for (const [what, hyp] of [['x <= x·x (a product of two rows)', atMost(x('x'), prod(x('x'), x('x')))], ['x·x <= x (false at x = 2)', atMost(prod(x('x'), x('x')), x('x'))]] as const) {
  const goal: Goal = {name: what, hyps: [not(hyp)]}
  const out = decideAll([goal]), real = out.ok ? undefined : concretize(goal)
  console.log(`  ${what.padEnd(46)} ${out.ok ? `PROVEN   ${out.leaves} leaves, kernel accepts` : real ? `REFUTED  at ${JSON.stringify(real)} (true arithmetic)` : `OPEN     ${out.stuck}`}`)
}

// Random integer systems of bands (lo <= a·x + b·y + c·z <= hi, coefficients up to 13, like Pugh's example), each
// variable within 0..6: the prover (with range splits) must refute exactly the empty ones,
// and the kernel must accept every refutation.
console.log('Integer completeness on bounded systems')
let seed = 7
const rand = (lo: number, hi: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return lo + (seed % (hi - lo + 1)) }
let agree = 0, refuted = 0, split = 0
const trials = 400
for (let t = 0; t < trials; t++) {
  const vars = ['x', 'y', 'z']
  const rows: C[] = vars.map(v => atMost(x(v), n(6)))
  for (let i = 0; i < 2; i++) {
    const pos = vars.reduce<E>((acc, v) => plus(acc, times(rand(0, 13), x(v))), n(0)), neg = vars.reduce<E>((acc, v) => plus(acc, times(rand(0, 13), x(v))), n(0))
    const lo = rand(0, 40), width = rand(0, 6)
    // lo <= pos − neg <= lo + width, over naturals: neg + lo <= pos and pos <= neg + lo + width
    rows.push(atMost(plus(neg, n(lo)), pos), atMost(pos, plus(neg, n(lo + width))))
  }
  const hyp = all(...rows)
  const values = (e: E, env: Record<string, number>): number => e.op === 'const' ? e.value : e.op === 'var' ? env[e.name]! : e.op === 'mul' ? e.k * values(e.a, env) : values((e as any).a, env) + values((e as any).b, env)
  let brute = false
  for (let a = 0; a <= 6 && !brute; a++) for (let b = 0; b <= 6 && !brute; b++) for (let c = 0; c <= 6 && !brute; c++) {
    const env = {x: a, y: b, z: c}
    brute = rows.every(r => r.op === '<=' && values(r.a, env) <= values(r.b, env))
  }
  const goal: Goal = {name: 'random', hyps: [hyp]}
  const out = grow(goal)
  const empty = 'tree' in out && check(goal, out.tree)
  if ('tree' in out && 'split' in out.tree) split++
  if (empty) refuted++
  if (empty === !brute && ('tree' in out || out.stuck === 'sat')) agree++
}
console.log(`  ${agree} / ${trials} agree with brute force (${refuted} empty, ${split} of them needed splits), none unknown`)

console.log('Nested loops (ranks compared in order)')
const grid: Loop = {
  name: 'every cell of an n × m grid', params: ['n', 'm'], inputs: [], state: {i: n(0), j: n(0)},
  while: less(x('i'), x('n')),
  body: {i: ite(less(x('j'), x('m')), x('i'), plus(x('i'), n(1))), j: ite(less(x('j'), x('m')), plus(x('j'), n(1)), n(0))},
}
for (const [what, rank] of [['rank n ∸ i alone', minus(x('n'), x('i'))], ['rank m ∸ j alone', minus(x('m'), x('j'))], ['ranks (n ∸ i, m ∸ j) in order', [minus(x('n'), x('i')), minus(x('m'), x('j'))]]] as const) {
  const out = decideAll(loopObligations(grid, [], rank as unknown as E | E[]))
  console.log(`  ${`grid walk, ${what}`.padEnd(46)} ${out.ok ? `HALTS    ${out.leaves} leaves, kernel accepts` : `NO       ${out.stuck}`}`)
}
