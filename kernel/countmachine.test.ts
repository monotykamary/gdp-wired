// Counts in a machine (CountMachine.lean's checkCMachine, kernel.ts's checkCountedLaws): the hand-built toy consensus
// accepted and true on its small instances, each guard refusing what only it refuses, and a fuzz: certificates and laws
// mutated, every accepted set of laws true on every reachable state of the small instances (count maps read at the
// request's view, a law's at the state), by brute force.
import {describe, expect, test} from 'bun:test'
import {type C, type E, type Law, type Machine, any, get, less, n, not, same, times, x} from '../core/machine.ts'
import {type CountCert, type CountInst, type MapRead, checkCountedLaws, checkMC, countedObligations, mcGoal, obligations} from './kernel.ts'
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
    expect(bad({}, {maps: {...toy.m.maps, 'votes#': 0}})).toThrow(/post name/)
    expect(bad({c: {j: 'x', key: 'n', below: x('size'), body: get('Vote', x('?chosen'))}})).toThrow(/doesn't declare/)
    expect(bad({c: {j: 'x', key: 'n', below: x('n'), body}})).toThrow(/doesn't declare/)
    expect(bad({c: {j: 'x', key: 'n', below: x('size'), body: get('quorum', x('n'))}})).toThrow(/doesn't declare/)
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
