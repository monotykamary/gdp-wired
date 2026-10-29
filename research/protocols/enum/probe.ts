// DuoAI-style enumeration as a probe (DESIGN.md, section 4): candidate invariants enumerated from a template over a few
// keys per sort, pruned by reachable samples, the survivors checked by gdp-wired's kernel. Nothing here is trusted or in
// the library; the kernel checks the final set as it checks any written invariant.
//   bun research/protocols/enum/probe.ts <protocol> [--lits 3] [--trials 400] [--depth 40] [--bound 2]
//       [--check none|houdini] [--ms 600000] [--show 40] [--out file.json]
//
// 1. Sorts: a union-find over the places the rule reads a key at (a map's plain key, each part of a composed key
//    N·a + b, a map's value where a key is compared with or written into it), as core/infer.ts's keySorts reads them.
//    A sort is a class holding a map's key place; it is ordered where two of its terms are compared by < or ≤.
// 2. Samples: random runs from the start (the rule's own draws at small bounds, its assumption met), every state kept.
// 3. The template: per sort, as many keys as the most places of that sort one map or the caller's law reads (two for an
//    ordered sort, whose order is a relation of two); every sub-template of it. Atoms: each map's cell at the
//    sub-template's keys (a yes/no where every sample's cells are 0 or 1), each scalar of yes/nos, each param or scalar
//    of a sort equal to a key, and for an ordered sort t ≤ u between its terms (keys, cells of that sort, its params
//    and scalars, 0). Keys of one sort are distinct, those of an ordered sort increasing (DuoAI's prefixes).
// 4. Enumeration (DistAI's and DuoAI's ∀ part): the clauses of at most `lits` literals true in every row (a sample at
//    an assignment of its keys to the sub-template's), minimal (no proper part true in every row), reading every key
//    of their sub-template, one per renaming of keys of one sort.
// 5. The check (`--check houdini`): every candidate and the safety law, each law's goals proven with every other law
//    assumed (kernel/prove.ts's proveLaw); the candidates a goal fails dropped, again until none fails (Houdini, which
//    is DuoAI's removal-only refinement). Then the set with the safety law through proveRule with the search off: the
//    kernel's proof, checked.
import {protocols, N} from '../models.ts'
import {type C, type E, type Law, type Machine, type State, evalC, interpret, seeded} from '../../../core/machine.ts'
import {allowed} from '../../../core/watch.ts'
import {proveRule} from '../../../core/dsl.ts'
import {proveLaw} from '../../../kernel/prove.ts'
import {writeFileSync} from 'node:fs'

const arg = (name: string, d?: string) => { const i = process.argv.indexOf(`--${name}`); return i < 0 ? d : process.argv[i + 1] }
const id = process.argv[2]!
const LITS = Number(arg('lits', '3')), TRIALS = Number(arg('trials', '2000')), DEPTH = Number(arg('depth', '40')), BOUND = Number(arg('bound', '2'))
const CHECK = arg('check', 'none'), MS = Number(arg('ms', '600000')), SHOW = Number(arg('show', '40')), OUT = arg('out')
const proto = protocols.find(p => p.id === id)
if (!proto) throw new Error(`no protocol ${id}`)
const r = proto.make(), m: Machine = r.machine, safety: Law[] = proto.laws(r)
const HELD = process.argv.includes('--held'), WIDE = process.argv.includes('--wide'), PLUS = process.argv.includes('--plus'), WEAKEN = Number(arg('weaken', '0'))
function held(ps: Record<string, number>, st: State): number[] {
  const out = new Set<number>(Object.values(ps))
  for (const x of Object.values(st.scalars)) out.add(x)
  for (const cells of Object.values(st.maps)) for (const [key, val] of cells) { out.add(val); for (let k = key; ; k = Math.floor(k / N)) { out.add(k % N); if (k < N) break } }
  return [...out].filter(x => x < N)
}
const t0 = performance.now(), lap = () => Math.round(performance.now() - t0)

// --- 1. sorts ----------------------------------------------------------------------------------------------------------
const parent = new Map<string, string>()
const find = (a: string): string => { const p = parent.get(a); if (p === undefined || p === a) return a; const q = find(p); parent.set(a, q); return q }
const union = (a: string, b: string) => { const x = find(a), y = find(b); if (x !== y) parent.set(x, y) }
const stateMaps = Object.keys(m.maps ?? {}), inputMaps = m.inputMaps ?? []
const isMap = (name: string) => stateMaps.includes(name) || inputMaps.includes(name)
const scalars = Object.keys(m.state), params = m.params
// A key's parts N^(k-1)·x1 + ... + xk over names, or undefined.
const parts = (key: E): string[] | undefined => {
  const lin = new Map<string, number>()
  const go = (e: E, c: number): boolean => {
    if (e.op === 'var') { lin.set(e.name, (lin.get(e.name) ?? 0) + c); return true }
    if (e.op === 'const') return e.value === 0
    if (e.op === 'mul') return go(e.a, c * e.k)
    if (e.op === 'add') return go(e.a, c) && go(e.b, c)
    return false
  }
  if (!go(key, 1)) return undefined
  const vs = [...lin].sort((a, b) => b[1] - a[1])
  return vs.every(([, c], i) => c === N ** (vs.length - 1 - i)) ? vs.map(([v]) => v) : undefined
}
const sig = new Map<string, number>() // map → the number of its key's parts
const ordered = new Set<string>()
type Scope = (v: string) => string
const node = (scope: Scope, e: E): string | undefined => (e.op === 'var' ? scope(e.name) : e.op === 'get' && isMap(e.map) ? `V:${e.map}` : undefined)
const leaves = (e: E): E[] => (e.op === 'if' ? [...leaves(e.then), ...leaves(e.else)] : [e])
const walkE = (e: E, scope: Scope): void => {
  switch (e.op) {
    case 'get': {
      if (isMap(e.map)) {
        const ps = parts(e.key)
        if (ps) { if (!inputMaps.includes(e.map)) sig.set(e.map, Math.max(sig.get(e.map) ?? 0, ps.length)); ps.forEach((v, i) => union(scope(v), `S:${e.map}:${ps.length}:${i}`)) }
      }
      walkE(e.key, scope); return
    }
    case 'if': walkC(e.c, scope); walkE(e.then, scope); walkE(e.else, scope); return
    case 'mul': walkE(e.a, scope); return
    case 'add': case 'sub': case 'min': case 'max': case 'prod': walkE(e.a, scope); walkE(e.b, scope); return
    case 'var': case 'const': return
  }
}
const walkC = (c: C, scope: Scope): void => {
  switch (c.op) {
    case '<': case '<=': case '=': {
      const a = node(scope, c.a), b = node(scope, c.b)
      if (a && b) { union(a, b); if (c.op !== '=') ordered.add(a) }
      // (a key compared with a composed key: k = N·a + b at a write at every key)
      if (c.op === '=' && c.a.op === 'var') { const each = scope(c.a.name), ps = parts(c.b); if (ps && ps.length > 1) ps.forEach((v, i) => union(scope(v), `${each}:${ps.length}:${i}`)) }
      walkE(c.a, scope); walkE(c.b, scope); return
    }
    case 'and': case 'or': c.xs.forEach(x => walkC(x, scope)); return
    case 'not': walkC(c.x, scope); return
    case 'all': { const own = new Set([c.key, ...(c.keys ?? [])]); walkC(c.c, v => (own.has(v) ? `Q:${c.key}:${v}` : scope(v))); return }
    case 'flag': return
  }
}
const plain: Scope = v => `v:${v}`
for (const [mp, w] of Object.entries(m.step.maps ?? {})) {
  if ('each' in w) {
    // the key of a write at every key is the map's key (all its parts, for a composed one: S:map:k:i; below)
    const own = (v: string) => (v === w.each ? `E:${mp}` : plain(v))
    walkE(w.value, own); for (const l of leaves(w.value)) { const n2 = node(own, l); if (n2) union(`V:${mp}`, n2) }
  } else {
    walkE({op: 'get', map: mp, key: w.key}, plain); walkE(w.value, plain)
    for (const l of leaves(w.value)) { const n2 = node(plain, l); if (n2) union(`V:${mp}`, n2) }
  }
}
for (const [s, e] of Object.entries(m.step.state ?? {})) { walkE(e, plain); for (const l of leaves(e)) { const n2 = node(plain, l); if (n2) union(`v:${s}`, n2) } }
for (const c of Object.values(m.step.flags ?? {})) walkC(c, plain)
if (m.assume) walkC(m.assume, plain)
// (a composed write at every key, E:map:k:i, is the map's composed place)
for (const mp of stateMaps) { const k = sig.get(mp) ?? 1; if (k > 1) for (let i = 0; i < k; i++) union(`E:${mp}:${k}:${i}`, `S:${mp}:${k}:${i}`); else union(`E:${mp}`, `S:${mp}:1:0`) }
const lawScope = (l: Law): Scope => { const own = new Set([l.forall, ...(l.keys ?? [])]); return v => (own.has(v) ? `L:${l.name}:${v}` : plain(v)) }
for (const l of safety) walkC(l.holds, lawScope(l))
for (const mp of stateMaps) if (!sig.has(mp)) sig.set(mp, 1)
const slot = (mp: string, i: number) => find(`S:${mp}:${sig.get(mp)}:${i}`)
const sorts = [...new Set(stateMaps.flatMap(mp => Array.from({length: sig.get(mp)!}, (_, i) => slot(mp, i))))]
const isOrdered = (s: string) => [...ordered].some(o => find(o) === s)
const sortName = (s: string) => `s${sorts.indexOf(s)}`
const valueSort = (mp: string) => { const s = find(`V:${mp}`); return sorts.includes(s) ? s : undefined }
const indSort = (v: string) => { const s = find(`v:${v}`); return sorts.includes(s) ? s : undefined }
const individuals = [...params, ...scalars].filter(v => indSort(v))
// a sort is bounded (keys below N) where an input of it is assumed below N, or where it is a composed key's lower part
const bounded = (s: string) => stateMaps.some(mp => sig.get(mp)! > 1 && slot(mp, sig.get(mp)! - 1) === s)
  || m.inputs.some(x => find(`v:${x}`) === s && JSON.stringify(m.assume ?? {}).includes(`{"op":"<","a":{"op":"var","name":"${x}"},"b":{"op":"const","value":${N}}}`))

// --- 2. samples --------------------------------------------------------------------------------------------------------
const run = interpret(m), rand = seeded(7)
type Sample = {params: Record<string, number>, st: State}
const samples: Sample[] = [], seen = new Set<string>()
const keep = (ps: Record<string, number>, st: State) => {
  const key = JSON.stringify([ps, st.scalars, Object.entries(st.maps).map(([k, v]) => [k, [...v].filter(([, x]) => x !== (st.defaults?.[k] ?? m.maps![k])).sort((a, b) => a[0] - b[0])]), st.defaults])
  if (!seen.has(key)) { seen.add(key); samples.push({params: ps, st}) }
}
for (let trial = 0; trial < TRIALS; trial++) {
  const bound = 1 + trial % BOUND + (trial % 7 === 6 ? 1 : 0)
  const ps = r.randomParams(rand, bound)
  if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) continue
  let st = run.init(ps)
  keep(ps, st)
  for (let d = 0, tries = 0; d < DEPTH && tries < DEPTH * 10; tries++) {
    const input = r.randomInput(rand, bound, ps)
    // (`--held`: half the numeric inputs drawn from the values the state holds, each key's parts, each cell, ±1, as
    // README.md's class E suggests: a request naming an epoch above a node's, a node voted for)
    if (HELD) { const hv = held(ps, st); for (const x of m.inputs) if (typeof input[x] === 'number' && x !== 'op' && hv.length && rand(2)) input[x] = Math.max(0, hv[rand(hv.length)]! + rand(3) - 1) }
    if (!allowed(m, run, ps, st, input)) continue
    // (a step that changes nothing, a request whose flag is false, is a stutter: drawn again, as DuoAI's samplers draw
    // only enabled actions)
    const next = run.step(ps, st, input), size = seen.size
    keep(ps, next)
    if (JSON.stringify([next.scalars, [...Object.values(next.maps)].map(c => [...c])]) === JSON.stringify([st.scalars, [...Object.values(st.maps)].map(c => [...c])])) continue
    d++
    st = next
    void size
  }
}
const tSamples = lap()

// --- 3. the template and its atoms -------------------------------------------------------------------------------------
const cellAt = (st: State, mp: string, key: number) => st.maps[mp]!.get(key) ?? st.defaults?.[mp] ?? m.maps![mp]!
const boolMap = (mp: string) => samples.every(s => { const d = s.st.defaults?.[mp] ?? m.maps![mp]!; return d <= 1 && [...s.st.maps[mp]!.values()].every(v => v <= 1) })
const boolScalar = (v: string) => samples.every(s => s.st.scalars[v]! <= 1)
const width = new Map<string, number>()
for (const s of sorts) {
  let w = Math.max(0, ...stateMaps.map(mp => Array.from({length: sig.get(mp)!}, (_, i) => slot(mp, i)).filter(x => x === s).length))
  for (const l of safety) w = Math.max(w, [l.forall, ...(l.keys ?? [])].filter(v => v && find(`L:${l.name}:${v}`) === s).length)
  if (isOrdered(s)) w = Math.max(w, 2)
  // (`--plus`: one key more for a sort one map reads at two places, as DuoAI generalizes vote_msg(N1, N1) ∧ vote_msg(N1, N2)
  // to N1, N2, N3: "one vote message per voter")
  if (PLUS && stateMaps.some(mp => Array.from({length: sig.get(mp)!}, (_, i) => slot(mp, i)).filter(x => x === s).length >= 2)) w += 1
  width.set(s, w)
}
type Var = {name: string, sort: string}
type Term = {text: string, e: E, at: (s: Sample, a: number[]) => number} // a value; `a` the keys, by the template's var index
// (`syms`, `sym`: the atom over free values of the terms it reads, to tell a tautology: t ≤ u ∨ u ≤ t)
type Atom = {text: string, c: C, vars: Set<number>, at: (s: Sample, a: number[]) => boolean, syms: string[], sym: (val: (t: string) => number) => boolean}
const v = (name: string): E => ({op: 'var', name}), k0 = (value: number): E => ({op: 'const', value})
function keyOf(vs: number[], vars: Var[]): E {
  return vs.reduce<E>((acc, x, i) => { const p = vs.length - 1 - i, t = p ? {op: 'mul', k: N ** p, a: v(vars[x]!.name)} as E : v(vars[x]!.name); return i === 0 ? t : {op: 'add', a: acc, b: t} }, k0(0))
}
const keyVal = (vs: number[], a: number[]) => vs.reduce((acc, x) => acc * N + a[x]!, 0)
const product = <T>(xs: T[][]): T[][] => xs.reduce<T[][]>((acc, ys) => acc.flatMap(p => ys.map(y => [...p, y])), [[]])
function atomsOf(vars: Var[]): Atom[] {
  const out: Atom[] = [], terms = new Map<string, (Term & {vars: Set<number>})[]>()
  const byS = (s: string) => vars.map((x, i) => [x, i] as const).filter(([x]) => x.sort === s).map(([, i]) => i)
  const addTerm = (s: string, t: Term & {vars: Set<number>}) => { if (!terms.has(s)) terms.set(s, []); terms.get(s)!.push(t) }
  for (const mp of stateMaps) {
    const places = Array.from({length: sig.get(mp)!}, (_, i) => byS(slot(mp, i)))
    for (const vs of product(places)) {
      const key = keyOf(vs, vars), cell: E = {op: 'get', map: mp, key}, text = `${mp}[${vs.map(x => vars[x]!.name).join(',')}]`
      const at = (s: Sample, a: number[]) => cellAt(s.st, mp, keyVal(vs, a))
      if (boolMap(mp)) out.push({text, c: {op: '<=', a: k0(1), b: cell}, vars: new Set(vs), at: (s, a) => at(s, a) >= 1, syms: [text], sym: val => val(text) >= 1})
      else { const vsrt = valueSort(mp); if (vsrt) addTerm(vsrt, {text, e: cell, at, vars: new Set(vs)}) }
    }
  }
  for (const sc of scalars) if (!indSort(sc) && boolScalar(sc)) out.push({text: sc, c: {op: '<=', a: k0(1), b: v(sc)}, vars: new Set(), at: s => s.st.scalars[sc]! >= 1, syms: [sc], sym: val => val(sc) >= 1})
  for (const ind of individuals) {
    const s = indSort(ind)!, at = (smp: Sample) => (params.includes(ind) ? smp.params[ind]! : smp.st.scalars[ind]!)
    if (isOrdered(s)) addTerm(s, {text: ind, e: v(ind), at, vars: new Set()})
    for (const x of byS(s)) out.push({text: `${ind}=${vars[x]!.name}`, c: {op: '=', a: v(ind), b: v(vars[x]!.name)}, vars: new Set([x]), at: (smp, a) => at(smp) === a[x], syms: [ind, vars[x]!.name], sym: val => val(ind) === val(vars[x]!.name)})
  }
  for (const s of sorts) {
    if (!isOrdered(s)) continue
    const ts: (Term & {vars: Set<number>, zero?: boolean, key?: boolean})[] = [...byS(s).map(x => ({text: vars[x]!.name, e: v(vars[x]!.name), at: (_: Sample, a: number[]) => a[x]!, vars: new Set([x]), key: true})), ...(terms.get(s) ?? []), {text: '0', e: k0(0), at: () => 0, vars: new Set<number>(), zero: true}]
    for (const t of ts) for (const u of ts) {
      if (t === u || t.zero || (t.key && u.key)) continue
      // (DuoAI's order atoms: a key against a cell, or two cells; params and scalars only equal to a key; a key or a cell
      // equal to 0, which our encoding's states before `init` need (Ivy's init is no step). `--wide`: every pair)
      if (!WIDE && !((t.key && !u.zero && !individuals.includes(u.text)) || (u.key && !individuals.includes(t.text)) || (!t.key && !u.key && !u.zero && !individuals.includes(t.text) && !individuals.includes(u.text)) || (u.zero && t.key) || (u.zero && !individuals.includes(t.text)))) continue
      if (u.zero) { out.push({text: `${t.text}=0`, c: {op: '=', a: t.e, b: u.e}, vars: t.vars, at: (smp, a) => t.at(smp, a) === 0, syms: [t.text], sym: val => val(t.text) === 0}); continue }
      out.push({text: `${t.text}<=${u.text}`, c: {op: '<=', a: t.e, b: u.e}, vars: new Set([...t.vars, ...u.vars]), at: (smp, a) => t.at(smp, a) <= u.at(smp, a), syms: [t.text, ...(u.zero ? [] : [u.text])], sym: val => val(t.text) <= (u.zero ? 0 : val(u.text))})
    }
  }
  return out
}

// The keys of a sort a sample holds: its cells' key parts and values of that sort, its individuals, 0..bound and one past.
function domain(smp: Sample, s: string): number[] {
  const ks = new Set<number>([0, 1, 2])
  for (const mp of stateMaps) {
    const k = sig.get(mp)!
    for (const [key, val] of smp.st.maps[mp]!) {
      let rest = key
      for (let i = k - 1; i >= 0; i--) { const d = i === 0 ? rest : rest % N; rest = Math.floor(rest / N); if (slot(mp, i) === s) ks.add(d) }
      if (valueSort(mp) === s) ks.add(val)
    }
  }
  for (const ind of individuals) if (indSort(ind) === s) ks.add(params.includes(ind) ? smp.params[ind]! : smp.st.scalars[ind]!)
  const xs = [...ks].filter(x => !bounded(s) || x < N).sort((a, b) => a - b)
  return [...xs, xs.at(-1)! + 1].filter(x => !bounded(s) || x < N)
}
function* assignments(smp: Sample, vars: Var[]): Generator<number[]> {
  const doms = new Map(sorts.map(s => [s, domain(smp, s)]))
  const a: number[] = new Array(vars.length)
  function* go(i: number): Generator<number[]> {
    if (i === vars.length) { yield a; return }
    const s = vars[i]!.sort, ord = isOrdered(s)
    for (const key of doms.get(s)!) {
      let ok = true
      for (let j = 0; j < i; j++) if (vars[j]!.sort === s && (ord ? a[j]! >= key : a[j] === key)) { ok = false; break }
      if (!ok) continue
      a[i] = key; yield* go(i + 1)
    }
  }
  yield* go(0)
}

// --- 4. enumeration ----------------------------------------------------------------------------------------------------
type Clause = {lits: [number, boolean][], text: string, law: Law, sub: string, at: number, ls: number[]}
const subData: {vars: Var[], atoms: Atom[], valid?: (ls: number[]) => boolean, lits?: {atom: number, pos: boolean}[], usable?: number[], make?: (ls: number[]) => Clause}[] = []
const clauses: Clause[] = [], stats: Record<string, unknown>[] = []
let nLaw = 0, tautologies = 0
const subs = product(sorts.map(s => Array.from({length: width.get(s)! + 1}, (_, i) => i))).filter(c => c.some(x => x > 0))
for (const counts of subs) {
  const vars: Var[] = sorts.flatMap((s, i) => Array.from({length: counts[i]!}, (_, j) => ({name: `${sortName(s)}_${j + 1}`, sort: s})))
  const atoms = atomsOf(vars)
  subData.push({vars, atoms})
  // rows: distinct atom vectors over the samples' assignments
  const rowSet = new Set<string>()
  for (const smp of samples) for (const a of assignments(smp, vars)) rowSet.add(atoms.map(t => (t.at(smp, a) ? '1' : '0')).join(''))
  const rows = [...rowSet], W = Math.ceil(rows.length / 32)
  // per literal (atom, sign): the rows where it is false, as a bitset
  const lits: {atom: number, pos: boolean, bad: Uint32Array}[] = []
  atoms.forEach((_, ai) => {
    for (const pos of [true, false]) {
      const bad = new Uint32Array(W)
      rows.forEach((row, ri) => { if ((row[ai] === '1') !== pos) bad[ri >> 5]! |= 1 << (ri & 31) })
      lits.push({atom: ai, pos, bad})
    }
  })
  const alwaysFalse = (bad: Uint32Array) => rows.length > 0 && bad.reduce((n, x) => n + popcount(x), 0) === rows.length
  const usable = lits.map((_, i) => i).filter(i => !alwaysFalse(lits[i]!.bad))
  const empty = (b: Uint32Array) => b.every(x => x === 0)
  const and = (a: Uint32Array, b: Uint32Array) => { const o = new Uint32Array(W); for (let i = 0; i < W; i++) o[i] = a[i]! & b[i]!; return o }
  const valid = (ls: number[]) => { let b = lits[ls[0]!]!.bad; for (const l of ls.slice(1)) b = and(b, lits[l]!.bad); return empty(b) }
  const found: number[][] = []
  const canon = new Set<string>()
  // permutations of keys within a sort that is not ordered (its keys are interchangeable)
  const perms = product(sorts.map(s => {
    const idx = vars.map((x, i) => [x, i] as const).filter(([x]) => x.sort === s).map(([, i]) => i)
    return isOrdered(s) ? [idx] : permutations(idx)
  })).map(ps => { const p = vars.map((_, i) => i); sorts.forEach((s, si) => { const idx = vars.map((x, i) => [x, i] as const).filter(([x]) => x.sort === s).map(([, i]) => i); idx.forEach((from, j) => { p[from] = ps[si]![j]! }) }); return p })
  const atomKey = new Map(atoms.map((t, i) => [t.text, i]))
  const renamed = (ls: number[], p: number[]) => ls.map(l => {
    const t = atoms[lits[l]!.atom]!
    let text = t.text
    text = text.replace(/s\d+_\d+/g, nm => { const i = vars.findIndex(x => x.name === nm); return `#${p[i]}` }).replace(/#(\d+)/g, (_, i) => vars[Number(i)]!.name)
    const ai = atomKey.get(text)
    return ai === undefined ? -1 : ai * 2 + (lits[l]!.pos ? 0 : 1)
  }).sort((a, b) => a - b).join(',')
  const dfs = (start: number, chosen: number[], bad: Uint32Array | undefined) => {
    for (let j = start; j < usable.length; j++) {
      const l = usable[j]!
      if (chosen.some(c => lits[c]!.atom === lits[l]!.atom)) continue
      const next = bad ? and(bad, lits[l]!.bad) : lits[l]!.bad, now = [...chosen, l]
      if (bad && next.every((x, i) => x === bad[i])) continue // (the literal adds nothing: a part is as strong)
      if (empty(next)) {
        // minimal: no proper part valid (the prefix isn't, by the search; check the others)
        if (now.length > 1 && now.some((_, i) => valid(now.filter((__, k) => k !== i)))) continue
        const used = new Set(now.flatMap(x => [...atoms[lits[x]!.atom]!.vars]))
        if (used.size !== vars.length) continue // (a smaller sub-template's)
        if (tautology(now.map(x => [atoms[lits[x]!.atom]!, lits[x]!.pos] as const), vars)) { tautologies++; continue }
        const key = perms.map(p => renamed(now, p)).sort()[0]!
        if (canon.has(key)) continue
        canon.add(key); found.push(now)
        continue
      }
      if (now.length < LITS) dfs(j + 1, now, next)
    }
  }
  dfs(0, [], undefined)
  stats.push({sub: vars.map(x => x.name).join(','), atoms: atoms.length, rows: rows.length, literals: usable.length, found: found.length})
  const make = (ls: number[]): Clause => {
    const body: C[] = ls.map(l => { const t = atoms[lits[l]!.atom]!; return lits[l]!.pos ? t.c : {op: 'not', x: t.c} })
    const guards: C[] = []
    vars.forEach((x, i) => {
      if (bounded(x.sort)) guards.push({op: '<', a: v(x.name), b: k0(N)})
      for (let j = 0; j < i; j++) if (vars[j]!.sort === x.sort) guards.push(isOrdered(x.sort) ? {op: '<', a: v(vars[j]!.name), b: v(x.name)} : {op: 'not', x: {op: '=', a: v(vars[j]!.name), b: v(x.name)}})
    })
    const holds: C = guards.length ? {op: 'or', xs: [{op: 'not', x: {op: 'and', xs: guards}}, ...body]} : (body.length === 1 ? body[0]! : {op: 'or', xs: body})
    const text = ls.map(l => `${lits[l]!.pos ? '' : '¬'}${atoms[lits[l]!.atom]!.text}`).join(' ∨ ')
    const name = `enum ${++nLaw}: ${vars.map(x => x.name).join(',')}. ${text}`
    const law: Law = {name, holds, forall: vars[0]!.name, ...(vars.length > 1 ? {keys: vars.slice(1).map(x => x.name)} : {})}
    return {lits: ls.map(l => [lits[l]!.atom, lits[l]!.pos]), text: `${vars.map(x => x.name).join(',')}. ${text}`, law, sub: vars.map(x => x.name).join(','), at: subData.length - 1, ls}
  }
  Object.assign(subData.at(-1)!, {valid, lits, usable, make})
  for (const ls of found) clauses.push(make(ls))
}
// A clause true at every value of the terms it reads (keys of an ordered sort increasing, of another distinct, cells
// and params any natural): no fact about the rule. Values 0..n−1 for n terms suffice for orders and equalities.
function tautology(ls: readonly (readonly [Atom, boolean])[], vars: Var[]): boolean {
  const syms = [...new Set(ls.flatMap(([t]) => t.syms))], n = syms.length, val = new Array<number>(n).fill(0)
  const idx = new Map(syms.map((x, i) => [x, i])), get = (x: string) => val[idx.get(x)!]!
  const keyIs = vars.map(x => idx.get(x.name))
  const ok = () => vars.every((x, i) => keyIs[i] === undefined || vars.slice(0, i).every((y, j) => y.sort !== x.sort || keyIs[j] === undefined || (isOrdered(x.sort) ? val[keyIs[j]!]! < val[keyIs[i]!]! : val[keyIs[j]!] !== val[keyIs[i]!])))
  const go = (i: number): boolean => {
    if (i === n) return !ok() || ls.some(([t, pos]) => t.sym(get) === pos)
    for (let x = 0; x < n; x++) { val[i] = x; if (!go(i + 1)) return false }
    return true
  }
  return go(0)
}
function popcount(x: number) { x -= (x >>> 1) & 0x55555555; x = (x & 0x33333333) + ((x >>> 2) & 0x33333333); return (((x + (x >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24 }
function permutations(xs: number[]): number[][] { return xs.length <= 1 ? [xs] : xs.flatMap((x, i) => permutations([...xs.slice(0, i), ...xs.slice(i + 1)]).map(p => [x, ...p])) }
const tEnum = lap()

// --- 4b. counterexamples by the interpreter (`--cti T`): Houdini on states near the samples ---------------------------
// A sample moved a little (a cell or a yes/no scalar flipped, a cell of a sort set to another of its keys) where every
// candidate alive and the safety law hold, stepped by a few random requests: a candidate a successor breaks is in no
// inductive subset of the candidates alive, so it is dropped (infer.ts's Houdini on the runs' neighbors, the same idea).
const holdsAt = (c: Clause, smp: Sample): boolean => {
  const {vars, atoms} = subData[c.at]!
  for (const a of assignments(smp, vars)) if (!c.lits.some(([ai, pos]) => atoms[ai]!.at(smp, a) === pos)) return false
  return true
}
const safeAt = (smp: Sample): boolean => safety.every(l => {
  const names = [l.forall, ...(l.keys ?? [])].filter((x): x is string => !!x)
  const doms = names.map(x => { const s = find(`L:${l.name}:${x}`); return sorts.includes(s) ? domain(smp, s) : [0, 1, 2, 3] })
  return product(doms).every(ks => evalC(l.holds, {...smp.params, ...Object.fromEntries(names.map((x, i) => [x, ks[i]!]))}, smp.st, m))
})
const CTI = Number(arg('cti', '0'))
let alive = clauses.slice()
const ctiStats = {tried: 0, lawful: 0, dropped: 0, safetyBroken: 0, ms: 0}
if (CTI) {
  const tc = performance.now(), rc = seeded(11)
  for (let t = 0; t < CTI && alive.length; t++) {
    ctiStats.tried++
    const base = samples[rc(samples.length)]!, st: State = {...base.st, scalars: {...base.st.scalars}, maps: Object.fromEntries(Object.entries(base.st.maps).map(([k, c]) => [k, new Map(c)]))}
    const smp: Sample = {params: base.params, st}
    for (let e = 0, edits = 1 + rc(3); e < edits; e++) {
      const bools = scalars.filter(x => !indSort(x) && boolScalar(x))
      if (bools.length && rc(6) === 0) { const x = bools[rc(bools.length)]!; st.scalars[x] = 1 - st.scalars[x]!; continue }
      const mp = stateMaps[rc(stateMaps.length)]!, k = sig.get(mp)!
      const key = Array.from({length: k}, (_, i) => { const d = domain(smp, slot(mp, i)); return d[rc(d.length)]! }).reduce((acc, x) => acc * N + x, 0)
      if (boolMap(mp)) st.maps[mp]!.set(key, cellAt(st, mp, key) ? 0 : 1)
      else { const vs = valueSort(mp); if (vs) { const d = domain(smp, vs); st.maps[mp]!.set(key, d[rc(d.length)]!) } }
    }
    if (!safeAt(smp) || !alive.every(c => holdsAt(c, smp))) continue
    ctiStats.lawful++
    for (let q = 0; q < 8; q++) {
      const input = r.randomInput(rc, BOUND + 1, smp.params)
      if (HELD) { const hv = held(smp.params, st); for (const x of m.inputs) if (typeof input[x] === 'number' && x !== 'op' && hv.length && rc(2)) input[x] = Math.max(0, hv[rc(hv.length)]! + rc(3) - 1) }
      if (!allowed(m, run, smp.params, st, input)) continue
      let next: State
      try { next = run.step(smp.params, st, input) } catch { continue }
      const after: Sample = {params: smp.params, st: next}
      const before = alive.length
      alive = alive.filter(c => holdsAt(c, after))
      ctiStats.dropped += before - alive.length
      if (!safeAt(after)) ctiStats.safetyBroken++
    }
  }
  ctiStats.ms = Math.round(performance.now() - tc)
}

const report: Record<string, unknown> = {
  id, samples: samples.length, samplesMs: tSamples, enumMs: tEnum - tSamples,
  sorts: sorts.map(s => ({sort: sortName(s), width: width.get(s), ordered: isOrdered(s), bounded: bounded(s), maps: stateMaps.flatMap(mp => Array.from({length: sig.get(mp)!}, (_, i) => (slot(mp, i) === s ? `${mp}.${i}` : '')).filter(Boolean)), values: stateMaps.filter(mp => valueSort(mp) === s), individuals: individuals.filter(x => indSort(x) === s)})),
  subtemplates: stats, candidates: clauses.length, tautologies, cti: {...ctiStats, alive: alive.length},
}
console.error(JSON.stringify(report, null, 1))
for (const c of alive.slice(0, SHOW)) console.error('  ', c.text)

// --- 5. the kernel ----------------------------------------------------------------------------------------------------
if (CHECK === 'houdini') {
  const kinds = r.kindLaws().filter((k: Law) => !safety.some(l => l.name === k.name))
  let kept = alive.map(c => c.law)
  const byName = new Map(alive.map(c => [c.law.name, c])), tried = new Set<string>()
  let weakened = 0
  const rounds: Record<string, unknown>[] = []
  const until = t0 + MS
  let safe = false
  for (let round = 0; performance.now() < until; round++) {
    const laws = [...kinds, ...kept, ...safety], failed = new Set<string>(), unknown = new Set<string>()
    const tr = performance.now()
    for (let i = kinds.length; i < laws.length && performance.now() < until; i++) {
      const tl = performance.now(), out = proveLaw(m, laws, i)
      if (process.argv.includes('--trace')) console.error(`law ${i - kinds.length + 1}/${laws.length - kinds.length} ${out.proven ? 'proven' : out.stuck} ${Math.round(performance.now() - tl)} ms ${laws[i]!.name.slice(0, 90)}`)
      if (!out.proven) { failed.add(laws[i]!.name); if (out.stuck !== 'sat') unknown.add(laws[i]!.name) }
    }
    const safetyFails = safety.some(l => failed.has(l.name))
    rounds.push({round, laws: kept.length, failed: failed.size, unknown: unknown.size, safetyFails, ms: Math.round(performance.now() - tr), dropped: [...failed].map(n => (unknown.has(n) ? `unknown: ${n}` : n))})
    console.error(JSON.stringify(rounds.at(-1)))
    const before = kept.length, w0 = weakened
    kept = kept.filter(l => !failed.has(l.name))
    // (`--weaken`: a dropped candidate's one-literal weakenings in its sub-template that every sample row still allows
    // and no candidate kept implies: DuoAI's co-implication refinement, one step down its implication graph)
    if (WEAKEN) {
      const keptC = kept.map(l => byName.get(l.name)!).filter(Boolean)
      for (const name of failed) {
        const c = byName.get(name); if (!c || c.ls.length >= LITS + WEAKEN) continue
        const sd = subData[c.at]!
        for (const l of sd.usable!) {
          if (c.ls.some(x => sd.lits![x]!.atom === sd.lits![l]!.atom)) continue
          const ls = [...c.ls, l].sort((a, b) => a - b), key = `${c.at}:${ls.join(',')}`
          if (tried.has(key) || !sd.valid!(ls)) continue
          tried.add(key)
          if (keptC.some(k => k.at === c.at && k.ls.every(x => ls.includes(x)))) continue
          const w = sd.make!(ls); w.law = {...w.law, name: `${w.law.name} (from ${name.split(':')[0]})`}
          byName.set(w.law.name, w); kept.push(w.law); keptC.push(w); weakened++
        }
      }
    }
    if (failed.size === 0) { safe = true; break }
    if (kept.length === before && safetyFails && weakened === w0) break // (only the safety law fails: the candidates don't suffice)
  }
  report.houdini = {rounds, kept: kept.length, inductive: safe, weakened, ms: lap() - tEnum}
  if (safe) {
    const tv = performance.now(), verdict = proveRule(r, [...kept, ...safety], {search: false})
    report.final = {proven: verdict.proven, checked: verdict.checked, goal: verdict.goal, stuck: verdict.stuck, ms: Math.round(performance.now() - tv), laws: kept.map(l => l.name)}
  }
}
report.totalMs = lap()
console.log(JSON.stringify(report))
if (OUT) writeFileSync(OUT, JSON.stringify({...report, clauses: clauses.map(c => c.text)}, null, 1))
