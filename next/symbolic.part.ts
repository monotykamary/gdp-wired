// --- symbolic: from expressions to cases of linear constraints -------------------------------------------------------

type Cases<T> = {path: Constraint[], value: T}[]
// How map reads resolve. A focus cell is a map cell the law under proof talks about, at a key expression; a read at a
// key equal to a focus key is that cell. Any other read is a cell named by its map and key (the same cell for the same
// key within one case), about which the laws that hold at every key are assumed.
type Focus = {map: string, key: Lin, cell: string}
type Reads = {focus: Focus[], other: (map: string, key: Lin) => {cell: string, assume: Constraint[][]}}
type Sym = {names: Record<string, Lin>, reads: Reads}

const cross = <A, B>(as: Cases<A>, f: (a: A) => Cases<B>): Cases<B> => as.flatMap(a => f(a.value).map(b => ({path: [...a.path, ...b.path], value: b.value})))
// Every way a key can differ from each of some focus keys.
const apartFrom = (key: Lin, keys: Lin[]): Constraint[][] => keys.reduce<Constraint[][]>((acc, f) => acc.flatMap(p => [[...p, ...lt(key, f)], [...p, ...lt(f, key)]]), [[]])

function symE(e: E, s: Sym): Cases<Lin> {
  switch (e.op) {
    case 'var': return [{path: [], value: s.names[e.name] ?? v(e.name)}]
    case 'const': return [{path: [], value: k(e.value)}]
    case 'add': return cross(symE(e.a, s), a => symE(e.b, s).map(b => ({path: b.path, value: add(a, b.value)})))
    case 'mul': return symE(e.a, s).map(a => ({path: a.path, value: scale(a.value, e.k)}))
    case 'sub': // truncated at 0, as on naturals
      return cross(symE(e.a, s), a => symE(e.b, s).flatMap(b => [
        {path: [...b.path, ...le(b.value, a)], value: sub(a, b.value)},
        {path: [...b.path, ...lt(a, b.value)], value: k(0)},
      ]))
    case 'min': case 'max':
      return cross(symE(e.a, s), a => symE(e.b, s).flatMap(b => {
        const aFirst = e.op === 'min' ? le(a, b.value) : le(b.value, a)
        const bFirst = e.op === 'min' ? lt(b.value, a) : lt(a, b.value)
        return [{path: [...b.path, ...aFirst], value: a}, {path: [...b.path, ...bFirst], value: b.value}]
      }))
    case 'if':
      return [...cross(symC(e.c, s, true), () => symE(e.then, s)), ...cross(symC(e.c, s, false), () => symE(e.else, s))]
    case 'get':
      return symE(e.key, s).flatMap(key => {
        const focus = s.reads.focus.filter(f => f.map === e.map)
        const at = focus.map(f => ({path: [...key.path, ...eq(key.value, f.key)], value: v(f.cell)}))
        const other = s.reads.other(e.map, key.value)
        const assumes = other.assume.length ? other.assume : [[]]
        const elsewhere = apartFrom(key.value, focus.map(f => f.key)).flatMap(apart => assumes.map(a => ({path: [...key.path, ...apart, ...a], value: v(other.cell)})))
        return [...at, ...elsewhere]
      })
  }
}
// The cases in which c has the given truth value.
function symC(c: C, s: Sym, truth: boolean): Cases<null> {
  switch (c.op) {
    case '<': case '<=': case '=':
      return cross(symE(c.a, s), a => symE(c.b, s).flatMap(b => {
        const [p, q] = [a, b.value]
        const holds = c.op === '<' ? (truth ? [lt(p, q)] : [le(q, p)])
          : c.op === '<=' ? (truth ? [le(p, q)] : [lt(q, p)])
          : truth ? [eq(p, q)] : [lt(p, q), lt(q, p)]
        return holds.map(constraints => ({path: [...b.path, ...constraints], value: null}))
      }))
    case 'not': return symC(c.x, s, !truth)
    case 'and': case 'or': {
      if ((c.op === 'and') === truth) return c.xs.reduce<Cases<null>>((acc, y) => cross(acc, () => symC(y, s, truth)), [{path: [], value: null}])
      return c.xs.flatMap(y => symC(y, s, truth))
    }
  }
}

// --- proofs ----------------------------------------------------------------------------------------------------------

export type Obligation = {phase: 'start' | 'step', law: string, constraints: Constraint[], verdict: Verdict}
export type Proof = {law: Law, proven: boolean, obligations: Obligation[]}

// The map reads a condition makes, as (map, key expression).
function readsOf(c: C): {map: string, key: E}[] {
  const inE = (e: E): {map: string, key: E}[] => e.op === 'get' ? [{map: e.map, key: e.key}, ...inE(e.key)]
    : e.op === 'if' ? [...readsOfC(e.c), ...inE(e.then), ...inE(e.else)] : 'a' in e ? [...inE(e.a), ...('b' in e ? inE(e.b) : [])] : []
  const readsOfC = (y: C): {map: string, key: E}[] => y.op === 'not' ? readsOfC(y.x) : y.op === 'and' || y.op === 'or' ? y.xs.flatMap(readsOfC) : [...inE(y.a), ...inE(y.b)]
  return readsOfC(c)
}
const keyLin = (e: E, names: Record<string, Lin>): Lin => symE(e, {names, reads: noReads})[0]!.value
const cellName = (map: string, key: Lin, when: string) => `${map}[${show(key)}]${when}`

// Proves `goal` by induction, assuming `invariants` (which include goal) hold before the step. A law with `forall`
// holds at every key; it is proven at a fresh key, and assumed at every key the step reads.
export function prove(m: Machine, goal: Law, invariants: Law[] = [goal]): Proof {
  const obligations: Obligation[] = []
  const naturals = [...m.params, ...m.inputs, ...Object.keys(m.state)]
  const assumeCases = m.assume ? symC(m.assume, {names: {}, reads: noReads}, true) : [{path: [], value: null}]
  const goalNames: Record<string, Lin> = goal.forall ? {[goal.forall]: v(`${goal.forall}*`)} : {}
  const forallLaws = invariants.filter(law => law.forall !== undefined)
  const scalarLaws = invariants.filter(law => law.forall === undefined)

  // At the start: every scalar and every map cell is its initial value.
  const startNames: Record<string, Lin> = {...goalNames}
  const startPath: Constraint[] = []
  for (const [name, e] of Object.entries(m.state)) {
    const [only] = symE(e, {names: {}, reads: noReads})
    startPath.push(...only!.path, ...eq(v(`${name}@0`), only!.value))
    startNames[name] = v(`${name}@0`)
  }
  const startReads: Reads = {focus: [], other: map => ({cell: `${map}@0`, assume: []})}
  for (const map of Object.keys(m.maps ?? {})) startPath.push(...eq(v(`${map}@0`), k(m.maps![map]!)))
  for (const a of assumeCases) for (const g of symC(goal.holds, {names: startNames, reads: startReads}, false)) {
    const constraints = [...nat(...m.params, ...Object.values(goalNames).flatMap(l => Object.keys(l))), ...a.path, ...startPath, ...g.path]
    obligations.push({phase: 'start', law: goal.name, constraints, verdict: solve(constraints)})
  }

  // The focus cells: every map read of the goal and of the scalar invariants, before and after the step.
  const focusReads = [...readsOf(goal.holds).map(r => ({...r, names: goalNames})), ...scalarLaws.flatMap(l => readsOf(l.holds).map(r => ({...r, names: {}})))]
  const focus: Focus[] = []
  for (const r of focusReads) {
    const key = keyLin(r.key, r.names)
    if (!focus.some(f => f.map === r.map && show(f.key) === show(key))) focus.push({map: r.map, key, cell: cellName(r.map, key, '')})
  }
  // The laws that hold at every key, at one key: the cells there are resolved by `cellAt`.
  const lawsAt = (key: Lin, cellAt: (map: string) => string): Constraint[][] => forallLaws.reduce<Constraint[][]>((acc, law) => {
    const cases = symC(law.holds, {names: {[law.forall!]: key}, reads: {focus: [], other: map => ({cell: cellAt(map), assume: []})}}, true)
    return acc.flatMap(p => cases.map(c => [...p, ...c.path]))
  }, [[]])
  const otherCell = (map: string, key: Lin) => cellName(map, key, '')
  const preReads: Reads = {focus, other: (map, key) => ({cell: otherCell(map, key), assume: lawsAt(key, mp => otherCell(mp, key))})}
  const preSym: Sym = {names: {...goalNames}, reads: preReads}

  // Assumptions before the step: the scalar invariants, the every-key laws at each focus key, and focus cells of one
  // map at equal keys being equal.
  let assumptions: Cases<null> = [{path: [], value: null}]
  for (const law of scalarLaws) assumptions = cross(assumptions, () => symC(law.holds, preSym, true))
  for (const f of focus) {
    const cases = lawsAt(f.key, mp => focus.find(g => g.map === mp && show(g.key) === show(f.key))?.cell ?? otherCell(mp, f.key))
    assumptions = cross(assumptions, () => cases.map(path => ({path, value: null})))
  }
  for (const [i, f] of focus.entries()) for (const g of focus.slice(i + 1).filter(g => g.map === f.map)) {
    assumptions = cross(assumptions, () => [
      {path: [...eq(f.key, g.key), ...eq(v(f.cell), v(g.cell))], value: null},
      ...apartFrom(f.key, [g.key]).map(path => ({path, value: null})),
    ])
  }

  // The step: each new scalar, and each focus cell after the step's write to its map.
  let stepCases: Cases<Record<string, Lin>> = [{path: [], value: {}}]
  for (const [name, e] of Object.entries(m.step.state ?? {})) stepCases = cross(stepCases, acc => symE(e, preSym).map(r => ({path: r.path, value: {...acc, [name]: r.value}})))
  for (const f of focus) {
    const write = m.step.maps?.[f.map]
    stepCases = cross(stepCases, acc => {
      if (write === undefined) return [{path: [], value: {...acc, [`${f.cell}'`]: v(f.cell)}}]
      return cross(symE(write.key, preSym), key => [
        ...symE(write.value, preSym).map(val => ({path: [...val.path, ...eq(key, f.key)], value: {...acc, [`${f.cell}'`]: val.value}})),
        ...apartFrom(key, [f.key]).map(apart => ({path: apart, value: {...acc, [`${f.cell}'`]: v(f.cell)}})),
      ])
    })
  }

  for (const a of assumeCases) for (const inv of assumptions) for (const st of stepCases) {
    const postNames: Record<string, Lin> = {...goalNames, ...Object.fromEntries(Object.keys(m.state).map(name => [name, st.value[name] ?? v(name)]))}
    const postFocus = focus.map(f => ({...f, cell: `${f.cell}'`}))
    const negated = symC(goal.holds, {names: postNames, reads: {focus: postFocus, other: noReads.other}}, false)
    for (const g of negated) {
      // The goal reads the focus cells after the step; replace each by its value.
      const path = g.path.map(c => ({...c, lin: postFocus.reduce((lin, f) => renameKey(lin, f.cell, st.value[f.cell]), c.lin)}))
      const all = [...a.path, ...inv.path, ...st.path, ...path]
      const vars = [...new Set(all.flatMap(c => Object.keys(c.lin).filter(key => key !== '1')))]
      const constraints = [...nat(...new Set([...naturals, ...vars])), ...all]
      obligations.push({phase: 'step', law: goal.name, constraints, verdict: solve(constraints)})
    }
  }
  return {law: goal, proven: obligations.every(o => o.verdict.kind === 'refuted'), obligations}
}

const noReads: Reads = {focus: [], other: map => ({cell: `${map}[?]`, assume: []})}
function renameKey(lin: Lin, from: string, to: Lin | undefined): Lin {
  if (!(from in lin) || to === undefined) return lin
  const {[from]: c, ...rest} = lin
  return add(rest, scale(to, c!))
}

