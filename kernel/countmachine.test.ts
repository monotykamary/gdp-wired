// Counts in a machine (CountMachine.lean's checkCMachine, kernel.ts's checkCountedLaws): the hand-built toy consensus
// accepted and true on its small instances, each guard refusing what only it refuses, and a fuzz: certificates and laws
// mutated, every accepted set of laws true on every reachable state of the small instances (count maps read at the
// request's view, a law's at the state), by brute force.
import {describe, expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, all, any, atMost, get, ite, less, n, not, plus, same, x} from '../core/machine.ts'
import {type CountCert, type CountInst, type MapRead, check, checkCountedLaws, checkLaws, checkMC, countedObligations, mcGoal, obligations} from './kernel.ts'
import {clock, grow} from './prove.ts'
import {countedProof, toyCounted} from '../lean-kernel/count-examples.ts'

const scale = Number(process.env.FUZZ_SCALE ?? 1)

// --- the meaning, by brute force -----------------------------------------------------------------------------------------
type Env = Record<string, number>
type Maps = Record<string, (k: number) => number>
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
    case 'get': return maps[e.map]?.(ev(e.key, env, maps)) ?? 0
  }
}
// (flags: decided in `env` as ?f, 0 or 1; a quantified flag over the keys below `keys`)
const holds = (c: C, env: Env, maps: Maps, keys = 8): boolean => {
  switch (c.op) {
    case '<': return ev(c.a, env, maps) < ev(c.b, env, maps)
    case '<=': return ev(c.a, env, maps) <= ev(c.b, env, maps)
    case '=': return ev(c.a, env, maps) === ev(c.b, env, maps)
    case 'not': return !holds(c.x, env, maps, keys)
    case 'and': return c.xs.every(y => holds(y, env, maps, keys))
    case 'or': return c.xs.some(y => holds(y, env, maps, keys))
    case 'flag': return env[`?${c.name}`] === 1
    case 'all': return Array.from({length: keys}, (_, k) => k).every(k => holds(c.c, {...env, [c.key]: k}, maps, keys))
  }
}
const countAt = (m: Machine, name: string, env: Env, maps: Maps) => (x0: number): number => {
  const d = m.counts![name]!, e1 = {...env, [d.j]: x0}
  let s = 0
  for (let k = 0; k < ev(d.below, e1, maps); k++) s += ev(d.body, {...e1, [d.key]: k}, maps)
  return s
}
const withCounts = (m: Machine, env: Env, maps: Maps): Maps => {
  const out: Maps = {...maps}
  for (const c of Object.keys(m.counts ?? {})) out[c] = countAt(m, c, env, maps)
  return out
}
type State = {cells: Record<string, number[]>}
const mapsOf = (st: State): Maps => Object.fromEntries(Object.entries(st.cells).map(([mp, cs]) => [mp, (k: number) => cs[k] ?? 0]))
// Every state the machine reaches from the start, each request's inputs over `inputs`, its carried maps over `carried`.
function reach(m: Machine, params: Env, inputs: Env[], carried: Record<string, number[]>[], width: number, cap = 4000): State[] {
  const start: State = {cells: Object.fromEntries(Object.entries(m.maps ?? {}).map(([mp, c]) => [mp, Array.from({length: width}, () => c)]))}
  const seen = new Map<string, State>([[JSON.stringify(start), start]]), queue = [start]
  while (queue.length && seen.size < cap) {
    const st = queue.shift()!
    for (const inp of inputs) for (const car of carried) {
      const base = {...params, ...inp}, maps0: Maps = {...mapsOf(st), ...Object.fromEntries(Object.entries(car).map(([mp, cs]) => [mp, (k: number) => cs[k] ?? 0]))}
      const maps = withCounts(m, base, maps0)
      const env: Env = {...base}
      for (const [f, c] of Object.entries(m.step.flags ?? {})) env[`?${f}`] = holds(c, env, maps, width) ? 1 : 0
      if (m.assume && !holds(m.assume, env, maps, width)) continue
      const next: State = {cells: Object.fromEntries(Object.entries(st.cells).map(([mp, cs]) => [mp, [...cs]]))}
      for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
        if ('each' in w) throw new Error('no write at every key here')
        const k = ev(w.key, env, maps)
        if (k < width) next.cells[mp]![k] = ev(w.value, env, maps)
      }
      const key = JSON.stringify(next)
      if (!seen.has(key)) { seen.set(key, next); queue.push(next) }
    }
  }
  return [...seen.values()]
}
// A law at a state: at every key (and further keys) below the width; its count maps the state's counts.
function lawHolds(m: Machine, law: Law, params: Env, st: State, width: number): boolean {
  const maps = withCounts(m, params, mapsOf(st)), keys = [law.forall, ...(law.keys ?? [])].filter((k): k is string => !!k)
  const go = (env: Env, ks: string[]): boolean => (ks.length ? Array.from({length: width}, (_, v) => v).every(v => go({...env, [ks[0]!]: v}, ks.slice(1))) : holds(law.holds, env, maps, width))
  return go({...params}, keys)
}
const subsets = (size: number): number[][] => Array.from({length: 1 << size}, (_, b) => Array.from({length: size}, (_, k) => (b >> k) & 1))
const toyStates = (m: Machine, size: number) => reach(m, {size}, [0, 1].flatMap(op => Array.from({length: size}, (_, i) => [0, 1].map(val => ({op, i, val}))).flat()), subsets(size).map(Q => ({Q})), size + 1)
const truly = (m: Machine, laws: Law[]): boolean => [2, 3].every(size => toyStates(m, size).every(st => laws.every(l => lawHolds(m, l, {size}, st, size + 1))))

// --- the example -----------------------------------------------------------------------------------------------------------
const toy = toyCounted()
const certs = countedProof(toy.m, toy.laws, toy.instances, toy.certs)
const proof = {instances: toy.instances, certs}
const stepOne = 'one value decided @step', stepMaj = 'a decided value has a majority @step'
const withCert = (name: string, f: (k: CountCert) => CountCert) => ({instances: toy.instances, certs: {...certs, [name]: f(certs[name]!)}})

describe('counts in a machine', () => {
  test('the toy consensus: accepted, and true on its small instances', () => {
    expect(checkCountedLaws(toy.m, toy.laws, proof)).toBe(true)
    expect(truly(toy.m, toy.laws)).toBe(true)
    // (the quorum guard is what makes it true: without it two values are decided)
    const noGuard: Machine = {...toy.m, assume: less(x('i'), x('size'))}
    expect(truly(noGuard, toy.laws)).toBe(false)
  })

  test('a machine with counts has no plain obligations; a law reads no count of the request', () => {
    expect(() => obligations(toy.m, toy.laws)).toThrow(/counts/)
    const viewLaw: Law = {name: 'reads the quorum', holds: less(n(0), get('quorum', n(0)))}
    expect(() => countedObligations(toy.m, [viewLaw])).toThrow(/quorum/)
  })

  test('the declarations: j and key apart and fresh, the post name free, the body reading no flag', () => {
    const bad = (counts: Machine['counts'], extra: Partial<Machine> = {}) => () => countedObligations({...toy.m, ...extra, counts: {...toy.m.counts, ...counts}}, toy.laws, toy.instances)
    const body = toy.m.counts!.votes!.body
    expect(bad({c: {j: 'k', key: 'k', below: x('size'), body}})).toThrow(/one name/)
    expect(bad({c: {j: 'i', key: 'n', below: x('size'), body}})).toThrow(/already a name/)
    expect(bad({c: {j: 'a', key: 'n', below: x('size'), body}})).toThrow(/already a name/)
    expect(bad({}, {maps: {...toy.m.maps, 'votes#': 0}})).toThrow(/reserved/)
    expect(bad({c: {j: 'x', key: 'n', below: x('size'), body: get('Vote', x('?chosen'))}})).toThrow(/doesn't declare/)
    expect(bad({c: {j: 'x', key: 'n', below: x('n'), body}})).toThrow(/doesn't declare/)
    expect(bad({c: {j: 'x', key: 'n', below: x('size'), body: get('quorum', x('n'))}})).toThrow(/doesn't declare/)
    // (a law's key, as the count would read it frozen at the state: Lean's cDeclOk refuses it too)
    expect(bad({c: {j: 'x', key: 'n', below: x('size'), body: get('Vote', x('a'))}})).toThrow(/doesn't declare/)
  })

  test('each guard on a certificate refuses what only it refuses', () => {
    // The witness a law's skolem, a further key, an input: the goal's instances at it don't hold at every value of it.
    for (const w of ['a#', 'b', 'i', 'size'])
      expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: k.insts.map((i, j) => (j === 0 ? {...i, wit: w} : i))})))).toBe(false)
    // Two instances with one witness.
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: k.insts.map(i => ({...i, wit: 'w1'}))})))).toBe(false)
    // A read's variable a witness, or its key term reading one.
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: k.reads.map((r, j) => (j === 0 ? ['w1', r[1], r[2]] as MapRead : r))})))).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: [...k.reads, ['cW', 'votes', x('w2')] as MapRead]})))).toBe(false)
    // A read of no declared count; the count after the step read as before it.
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: k.reads.map((r, j) => (j === 0 ? [r[0], 'Vote', r[2]] as MapRead : r))})))).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepMaj, k => ({...k, reads: k.reads.map(r => (r[0] === 'cA1' ? [r[0], 'votes', r[2]] as MapRead : r))})))).toBe(false)
    // A read's variable read by the goal, or two reads with one variable.
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: k.reads.map((r, j) => (j === 0 ? ['val', r[1], r[2]] as MapRead : r))})))).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: k.reads.map((r, j) => (j === 1 ? ['cA', r[1], r[2]] as MapRead : r))})))).toBe(false)
    // Coefficients that aren't safe integers, and input of the wrong shape.
    for (const z of [1.5, Number.NaN, 2 ** 53])
      expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: k.insts.map(i => ({...i, terms: i.terms.map(([, v]) => [z, v] as [number, string])}))})))).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: k.insts.map(i => ({...i, unit: 0.5}))})))).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: k.reads.map(r => [r[0], r[1]] as unknown as MapRead)})))).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: k.insts.map(i => ({...i, wit: 7 as unknown as string}))})))).toBe(false)
    // A goal without its certificate.
    const {[stepOne]: _, ...rest} = certs
    expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: rest})).toBe(false)
  })

  test('a count read after the step is the count there: a false law the stale read would prove', () => {
    // "no value has a vote": false (a cast gives one); read with the count before the step, its step goal would be
    // a tautology. The goals read it at votes#, whose body reads the vote just cast.
    const law: Law = {name: 'no votes', forall: 'a', holds: same(get('votes', x('a')), n(0))}
    expect(truly(toy.m, [law])).toBe(false)
    const [, step] = countedObligations(toy.m, [law], {'no votes': {'no votes': [x('a#')]}})
    expect(JSON.stringify(step!.goal.hyps.at(-1))).toContain('votes#')
    const stale = {...step!.goal, hyps: step!.goal.hyps.map(h => JSON.parse(JSON.stringify(h).replaceAll('"votes#"', '"votes"')) as C)}
    const o = grow(stale)
    expect('tree' in o).toBe(true)
    const k: CountCert = {reads: [], insts: [], tree: (o as {tree: CountCert['tree']}).tree}
    expect(checkMC(step!.goal.hyps, step!.decls, k)).toBe(false)
  })
})


// --- pointed: each guard on its own, a certificate whose tree the rest of the check accepts --------------------------------
// A variant of the toy (more counts, a precondition), its named certificates changed by `f`, the trees regrown; the
// tree must check against the goal mcGoal builds (what the kernel would accept with no guard), and the kernel refuses.
type Named = Record<string, {reads: MapRead[], insts: CountInst[]}>
const regrow = (m: Machine, laws: Law[], instances: typeof toy.instances, named: Named): Record<string, CountCert> | undefined => {
  const out: Record<string, CountCert> = {}
  for (const {goal: g, decls} of countedObligations(m, laws, instances)) {
    const k = named[g.name]!, goal = mcGoal(g.hyps, decls, k)
    const o = goal && grow(goal, new Map(), {nodes: 0, until: clock() + 20_000})
    if (!o || !('tree' in o) || !check(goal!, o.tree)) return undefined
    out[g.name] = {reads: k.reads, insts: k.insts, tree: o.tree}
  }
  return out
}
const refusedOnly = (m: Machine, laws: Law[], instances: typeof toy.instances, named: Named) => {
  const cs = regrow(m, laws, instances, named)
  expect(cs).toBeDefined()
  expect(checkCountedLaws(m, laws, {instances, certs: cs!})).toBe(false)
}
const addRead = (g: string, r: MapRead): Named => ({...toy.certs, [g]: {...toy.certs[g]!, reads: [...toy.certs[g]!.reads, r]}})
// (a param only one count's bound reads, a count whose body reads one only it reads, a count of every key below a bound)
const wide: Machine = {...toy.m, params: [...toy.m.params, 'lim', 'lim2'],
  counts: {...toy.m.counts, below: {j: 'x3', key: 'n3', below: x('lim'), body: n(1)}, fixed: {j: 'x4', key: 'n4', below: x('size'), body: get('Vote', x('lim2'))}}}
const b = x('b'), atLeast2 = atMost(n(2), x('size'))

describe('pointed', () => {
  test('a plain machine has its plain obligations', () => {
    const plain: Machine = {...toy.m, counts: undefined, assume: less(x('i'), x('size'))}
    expect(() => obligations(plain, [{name: 'decided is 0 or 1', forall: 'a', holds: toy.laws[0]!.holds}])).not.toThrow()
  })
  test('a law reads only a count of the state: its bound and body read no input and no carried map', () => {
    const law = (c: string): Law => ({name: 'reads it', holds: less(n(0), get(c, n(0)))})
    const body = toy.m.counts!.votes!.body
    for (const c of [{j: 'x5', key: 'n5', below: x('i'), body}, {j: 'x5', key: 'n5', below: x('size'), body: get('Vote', x('val'))}, {j: 'x5', key: 'n5', below: x('size'), body: get('Q', x('n5'))}])
      expect(() => countedObligations({...toy.m, counts: {...toy.m.counts, c5: c}}, [law('c5')])).toThrow(/c5/)
    expect(() => countedObligations({...toy.m, counts: {...toy.m.counts, c5: {j: 'x5', key: 'n5', below: x('size'), body: get('Vote', x('n5'))}}}, [law('c5')])).not.toThrow()
  })
  test('a count is over the naturals', () => {
    expect(() => countedObligations({...toy.m, counts: {...toy.m.counts, c5: {j: 'x5', key: 'n5', below: x('size'), body: n(-1)}}}, toy.laws)).toThrow(/negative/)
    expect(() => countedObligations({...toy.m, counts: {...toy.m.counts, c5: {j: 'x5', key: 'n5', below: {op: 'mul', k: -1, a: x('size')}, body: n(1)}}}, toy.laws)).toThrow(/negative/)
  })
  test('countedObligations refuses what obligations refuses, and builds one law\'s goals', () => {
    expect(() => countedObligations({...toy.m, maps: {...toy.m.maps, Vote: -1}}, toy.laws)).toThrow(/negative/)
    expect(() => countedObligations({...toy.m, step: {...toy.m.step, flags: {...toy.m.step.flags, neg: same(x('op'), n(-2))}}}, toy.laws)).toThrow(/negative/)
    expect(() => countedObligations(toy.m, [{name: 'about a request', holds: less(x('val'), n(9))}])).toThrow(/request/)
    expect(() => countedObligations(toy.m, [...toy.laws, {name: 'about a request', holds: less(x('val'), n(9))}])).toThrow(/request/)
    expect(() => countedObligations({...toy.m, step: {...toy.m.step, maps: {...toy.m.step.maps, Vote: {key: x('i'), value: n(-1)}}}}, toy.laws)).toThrow(/negative/)
    expect(() => countedObligations({...toy.m, facts: [{name: 'negative fact', holds: same(x('size'), n(-1))}]}, toy.laws)).toThrow(/negative/)
    expect(() => countedObligations(toy.m, [...toy.laws, {name: 'negative', holds: same(x('size'), n(-1))}])).toThrow(/negative/)
    expect(() => countedObligations({...toy.m, sums: {s: {key: 'k', term: get('Vote', x('k'))}}}, toy.laws)).toThrow(/sums/)
    expect(countedObligations(toy.m, toy.laws, toy.instances, 1).map(o => o.goal.name)).toEqual(['a decided value has a majority @start', 'a decided value has a majority @step'])
  })
  test('the step goal assumes the precondition', () => {
    // (the assumption gives size ≥ 1; the precondition size ≥ 2, which the step needs where it decides)
    const pm: Machine = {...toy.m, pre: atLeast2}
    const laws: Law[] = [...toy.laws, {name: 'a decision below size', forall: 'a', holds: atMost(plus(get('Decision', x('a')), n(1)), x('size'))}]
    const inst = {...toy.instances, 'a decision below size': {'a decision below size': [x('a#')], 'decided is 0 or 1': [x('a#')]}}
    const named: Named = {...toy.certs, 'a decision below size @start': {reads: [], insts: []}, 'a decision below size @step': {reads: [], insts: []}}
    expect(regrow(pm, laws, inst, named)).toBeDefined()
    expect(checkCountedLaws(pm, laws, {instances: inst, certs: regrow(pm, laws, inst, named)!})).toBe(true)
  })
  test('a read: its variable fresh for the hypotheses, the counts\' bounds and bodies, their j and key, the other reads', () => {
    const one = 'one value decided @step'
    // (?chosen only the hypotheses read; op a count after the step reads too, as the step reads it)
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['?chosen', 'votes', x('a#')]))
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['op', 'votes', b]))
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['lim', 'votes', b]))
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['lim2', 'votes', b]))
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['x2', 'votes', b]))
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['n3', 'votes', b]))
    refusedOnly(wide, toy.laws, toy.instances, {...toy.certs, [one]: {...toy.certs[one]!, reads: [...toy.certs[one]!.reads, ['z1', 'votes', b], ['z2', 'votes', x('z1')]]}})
    // twice the same variable; a key term reading a count's key
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['cA', 'votes', b]))
    refusedOnly(wide, toy.laws, toy.instances, addRead(one, ['z3', 'votes', x('n')]))
  })
  test('a read is a name, a map\'s name and a term', () => {
    const one = 'one value decided @step'
    for (const r of [['z4', 'votes', b, 'more'], [5, 'votes', b], ['z4', 7, b], ['z4', 'votes', 'b'], ['z4', 'votes', null]] as unknown as MapRead[])
      expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: {...certs, [one]: {...certs[one]!, reads: [...certs[one]!.reads, r]}}})).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: {...certs, [one]: {...certs[one]!, reads: {} as unknown as MapRead[]}}})).toBe(false)
    expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: {...certs, [one]: {...certs[one]!, insts: {} as unknown as CountInst[]}}})).toBe(false)
  })
  test('a term of a certificate: each constructor over the naturals, its edges accepted', () => {
    const one = 'one value decided @step', with1 = (t: E) => addRead(one, ['z8', 'votes', t])
    const ok = (t: E) => { const cs = regrow(toy.m, toy.laws, toy.instances, with1(t)); expect(cs).toBeDefined(); expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: cs!})).toBe(true) }
    // (refused: the tree grown with b at the place, the read's term swapped; the tree never reads that read)
    const grown = regrow(toy.m, toy.laws, toy.instances, with1(b))!
    const bad = (t: E) => {
      const k = grown[one]!, swapped = {...k, reads: k.reads.map((r, j) => (j === k.reads.length - 1 ? [r[0], r[1], t] as MapRead : r))}
      expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: {...grown, [one]: swapped}})).toBe(false)
    }
    expect(checkCountedLaws(toy.m, toy.laws, {instances: toy.instances, certs: grown})).toBe(true)
    const half = n(0.5), neg = n(-1)
    for (const t of [{op: 'mul', k: 0, a: b} as E, get('Vote', b), plus(b, n(0)), ite(less(b, n(2)), b, n(0)), ite(atMost(b, b), b, b), ite(same(b, b), b, b),
      ite(not(same(b, n(1))), b, b), ite(all(same(b, b), less(n(0), n(1))), b, b), ite(any(same(b, b), same(b, n(1))), b, b)]) ok(t)
    for (const t of [{op: 'mul', k: -1, a: b} as E, {op: 'mul', k: 1, a: half} as E, get('Vote', half), {op: 'get', map: 3, key: b} as unknown as E, plus(b, neg), plus(neg, b),
      ite(same(b, half), b, b), ite(less(half, b), b, b), ite(atMost(b, neg), b, b), ite(same(b, b), half, b), ite(same(b, b), b, neg),
      ite(not(same(b, half)), b, b), ite(all(same(b, b), same(b, half)), b, b), ite(any(same(b, half), same(b, b)), b, b),
      ite({op: 'and', xs: 'no'} as unknown as C, b, b), ite({op: 'flag', name: 'chosen'} as C, b, b), {op: 'var', name: 7} as unknown as E]) bad(t)
  })
  test('a read is no witness and reads none', () => {
    const one = 'one value decided @step'
    refusedOnly(toy.m, toy.laws, toy.instances, addRead(one, ['z5', 'votes', x('w1')]))
    // (a read named as the witness: its count reads the witness as its variable)
    const named: Named = {...toy.certs, [one]: {reads: [...toy.certs[one]!.reads, ['w9', 'votes', b]], insts: [...toy.certs[one]!.insts, {wit: 'w9', below: x('size'), terms: [[1, 'cA']], unit: 0}]}}
    refusedOnly(toy.m, toy.laws, toy.instances, named)
  })
  test('a witness: a name the machine and its laws don\'t read, the counts\' key not either', () => {
    const one = 'one value decided @step'
    // the witness the param size: the instance's second half is false, so it claims the sum is not positive
    const atSize: Named = {...toy.certs, [one]: {...toy.certs[one]!, insts: toy.certs[one]!.insts.map((i, j) => (j === 0 ? {...i, wit: 'size'} : i))}}
    refusedOnly(toy.m, toy.laws, toy.instances, atSize)
    const inst = {...toy.instances, 'one value decided': {...toy.instances['one value decided']!, '?chosen': [x('n'), x('w2')]}}
    const atKey: Named = {...toy.certs, [one]: {...toy.certs[one]!, insts: toy.certs[one]!.insts.map((i, j) => (j === 0 ? {...i, wit: 'n'} : i))}}
    refusedOnly(toy.m, toy.laws, inst, atKey)
  })
  test('checkMC on its own: a declaration\'s j and key apart', () => {
    const k = certs[stepOne]!, g = countedObligations(toy.m, toy.laws, toy.instances).find(o => o.goal.name === stepOne)!
    expect(checkMC(g.goal.hyps, g.decls, k)).toBe(true)
    expect(checkMC(g.goal.hyps, g.decls.map(d => (d.map === 'quorum' ? {...d, j: d.key} : d)), k)).toBe(false)
  })
})

// --- terra's review (gen/laneK2): a law's fresh name k# captured; certificate terms over the naturals; fact keys -----------
describe('names a goal reads by', () => {
  test('a law is proven at k#: no further key and no name of the machine may be k#', () => {
    // Before: ∀ k, k#. k = k# read k as k# (k# = k#), and a state named k# made ∀ k. k = 0 read 0 = 0 at the start.
    const plain: Machine = {name: 'empty', params: [], inputs: [], state: {}, step: {}}
    const capture: Law = {name: 'every two naturals equal', forall: 'k', keys: ['k#'], holds: same(x('k'), x('k#'))}
    expect(() => obligations(plain, [capture])).toThrow(/reserved/)
    const tree = {leaf: [{kind: 'input', index: 0}]} as unknown as CountCert['tree']
    expect(() => checkLaws(plain, [capture], {instances: {}, trees: {'every two naturals equal @start': tree, 'every two naturals equal @step': tree}})).toThrow(/reserved/)
    expect(() => obligations({...plain, state: {'k#': n(0)}}, [{name: 'all zero', forall: 'k', holds: same(x('k'), n(0))}])).toThrow(/reserved/)
    expect(() => countedObligations({...toy.m, maps: {...toy.m.maps, 'V#': 0}}, toy.laws)).toThrow(/reserved/)
    expect(() => countedObligations(toy.m, [...toy.laws, capture])).toThrow(/reserved/)
  })
  test('a read\'s key term and an instance\'s bound are terms over the naturals', () => {
    for (const t of [n(0.5), n(-1), n(2 ** 53), {op: 'mul', k: 0.5, a: x('b')}, {op: 'bogus'}] as E[]) {
      expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, reads: [...k.reads, ['z6', 'votes', t] as MapRead]})))).toBe(false)
      expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: [...k.insts, {wit: 'w7', below: t, terms: [], unit: 0}]})))).toBe(false)
    }
    expect(checkCountedLaws(toy.m, toy.laws, withCert(stepOne, k => ({...k, insts: [...k.insts, null as unknown as CountInst]})))).toBe(false)
  })
  test('a fact\'s key is no witness and no count\'s j or key', () => {
    const fm: Machine = {...toy.m, facts: [{name: 'every natural is itself', forall: 'w8', holds: same(x('w8'), x('w8'))}]}
    expect(checkCountedLaws(fm, toy.laws, proof)).toBe(true)
    expect(checkCountedLaws(fm, toy.laws, withCert(stepOne, k => ({...k, insts: [...k.insts, {wit: 'w8', below: x('size'), terms: [], unit: 0}]})))).toBe(false)
    expect(() => countedObligations({...fm, counts: {...fm.counts, c9: {j: 'w8', key: 'n9', below: x('size'), body: n(1)}}}, toy.laws)).toThrow(/already a name/)
  })
})

// --- fuzz: mutated certificates and laws, every acceptance true ---------------------------------------------------------
const rnd = (seed: number) => { let s = seed; return (k: number) => { s = (s * 1103515245 + 12345) % 2 ** 31; return Math.floor(s / 2 ** 31 * k) } }
const mutateLaw = (l: Law, r: (k: number) => number): Law => {
  const t = JSON.stringify(l.holds)
  const options = [t.replace('"op":"<"', '"op":"<="'), t.replace('"k":2', '"k":1'), t.replace('"value":1}', '"value":2}'), t.replace('"name":"size"', '"name":"a"'), t]
  return {...l, holds: JSON.parse(options[r(options.length)]!) as C}
}
const mutateCert = (k: CountCert, r: (k: number) => number): CountCert => {
  const w = ['w1', 'w2', 'w3', 'a#', 'b', 'val', 'cQ'], maps = ['votes', 'votes#', 'quorum', 'Vote']
  const terms = [x('a#'), x('b'), x('val'), n(0), x('w1')]
  const reads = k.reads.map(rd => (r(4) ? rd : [rd[0], maps[r(maps.length)]!, terms[r(terms.length)]!] as MapRead))
  const insts = k.insts.map((i): CountInst => (r(3) ? i : {...i, wit: w[r(w.length)]!, unit: i.unit + r(3) - 1, terms: i.terms.map(([z, v]) => [z + r(3) - 1, v] as [number, string])}))
  return {...k, reads, insts}
}

describe('fuzz', () => {
  test('every accepted mutation is true on the small instances', () => {
    let accepted = 0, tried = 0
    const until = clock() + 240_000 * scale
    for (let seed = 1; seed <= 60 * scale && clock() < until; seed++) {
      const r = rnd(seed)
      const laws = toy.laws.map(l => (r(3) ? l : mutateLaw(l, r)))
      const named = Object.fromEntries(Object.entries(toy.certs).map(([g, k]) => [g, r(2) ? k : mutateCert({...k, tree: {leaf: []}}, r)]))
      let ok = true
      const cs: Record<string, CountCert> = {}
      try {
        for (const {goal: g, decls} of countedObligations(toy.m, laws, toy.instances)) {
          const k = named[g.name]!, goal = mcGoal(g.hyps, decls, k)
          const o = goal && grow(goal, new Map(), {nodes: 0, until: clock() + 5_000})
          if (!o || !('tree' in o)) { ok = false; break }
          cs[g.name] = {reads: k.reads, insts: k.insts, tree: o.tree}
        }
      } catch { ok = false }
      tried++
      if (!ok || !checkCountedLaws(toy.m, laws, {instances: toy.instances, certs: cs})) continue
      accepted++
      expect(truly(toy.m, laws)).toBe(true)
    }
    console.log(`fuzz: ${tried} mutations, ${accepted} accepted, each true on the small instances`)
    expect(tried).toBeGreaterThan(10)
    expect(accepted).toBeGreaterThan(0)
  }, 600_000)
})
