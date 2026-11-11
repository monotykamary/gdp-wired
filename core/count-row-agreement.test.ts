import {expect, test} from 'bun:test'
import {type Law, type Machine, all, any, get, n, not, same, x} from './machine.ts'
import {type RowAgreementShape} from './row-agreement-shape.ts'
import {type RowAgreementTrace, proveRowAgreementCase, proposeRowAgreementInitial, rowAgreementWrittenKeys} from './count-row-agreement.ts'
import {certFor} from './counts.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withWall} from '../kernel/prove.ts'
function fixture() {
  const cell = (row: string) => get('cells', {op: 'add', a: {op: 'mul', k: 8, a: x(row)}, b: x('c')})
  const guard = all(...['a', 'b', 'c'].map(name => ({op: '<' as const, a: x(name), b: x('size')})), same(get('version', x('a')), get('version', x('b'))), same(get('epoch', x('a')), get('epoch', x('b'))), same(get('marker', x('a')), n(1)), same(get('marker', x('b')), n(1)))
  const law: Law = {name: 'versioned rows', forall: 'a', keys: ['b', 'c'], holds: any(not(guard), same(cell('a'), cell('b')))}
  const m: Machine = {name: 'plain frame', params: ['size'], inputs: [], state: {}, maps: {cells: 0, version: 0, epoch: 0, marker: 0}, pre: all({op: '<=', a: n(1), b: x('size')}, {op: '<=', a: x('size'), b: n(8)}), step: {}}
  const shape: RowAgreementShape = {map: 'cells', width: 8, left: 'a', right: 'b', column: 'c', fields: ['version', 'epoch'], markers: [{map: 'marker', value: 1}], guard}
  return {m, law, shape}
}
test('written-row discovery sees inlined operation guards and excludes inactive writes', () => {
  const {m, shape} = fixture(); m.inputs = ['op', 'i', 'j']; m.assume = same(x('op'), n(1))
  const self = get('version', x('row'))
  m.step.maps = {version: {each: 'row', value: {op: 'if', c: all(same(x('op'), n(1)), same(x('row'), x('i'))), then: n(1), else: {op: 'if', c: all(same(x('op'), n(2)), same(x('row'), x('j'))), then: n(2), else: {op: 'if', c: same(x('op'), n(0)), then: self, else: self}}}}}
  expect(rowAgreementWrittenKeys(m, shape)).toEqual(['i'])
  m.assume = same(x('op'), n(2)); expect(rowAgreementWrittenKeys(m, shape)).toEqual(['j'])
  delete m.assume; expect(rowAgreementWrittenKeys(m, shape)).toEqual([])
})
test('written-row discovery expands raw flags before consulting the kernel', () => {
  const {m, shape} = fixture(); m.inputs = ['op', 'i', 'j']; m.assume = same(x('op'), n(1))
  m.step.flags = {unused: same(x('op'), n(0)), quant: {op: 'all', key: 'member', c: same(get('marker', x('member')), n(1))}, active: all(same(x('op'), n(1)), {op: 'flag', name: 'quant'}), other: same(x('op'), n(2))}
  m.step.maps = {version: {each: 'row', value: {op: 'if', c: all({op: 'flag', name: 'active'}, same(x('row'), x('i'))), then: n(1), else: {op: 'if', c: all({op: 'flag', name: 'other'}, same(x('row'), x('j'))), then: n(2), else: get('version', x('row'))}}}}
  expect(rowAgreementWrittenKeys(m, shape)).toEqual(['i'])
  m.assume = same(x('op'), n(2)); expect(rowAgreementWrittenKeys(m, shape)).toEqual(['j'])
})
test('written-row discovery includes active point writes, not unrelated operations', () => {
  const {m, shape} = fixture(); m.inputs = ['op', 'i']; m.assume = same(x('op'), n(1))
  m.step.flags = {idle: same(x('op'), n(0)), copy: same(x('op'), n(1)), other: same(x('op'), n(2))}
  m.step.maps = {marker: {key: x('i'), value: {op: 'if', c: {op: 'flag', name: 'copy'}, then: n(1), else: get('marker', x('i'))}}}
  expect(rowAgreementWrittenKeys(m, shape)).toEqual(['i'])
  m.assume = same(x('op'), n(2)); expect(rowAgreementWrittenKeys(m, shape)).toEqual([])
  m.step.maps.marker = {key: x('i'), value: n(1)}; expect(rowAgreementWrittenKeys(m, shape)).toEqual(['i'])
})
test('written-row discovery retains a row equality outside its operation guard', () => {
  const {m, shape} = fixture(); m.inputs = ['op', 'i']; m.assume = same(x('op'), n(1))
  m.step.maps = {marker: {each: 'row', value: {op: 'if', c: same(x('row'), x('i')), then: {op: 'if', c: same(x('op'), n(1)), then: n(1), else: {op: 'if', c: same(x('op'), n(2)), then: n(1), else: {op: 'if', c: same(x('op'), n(0)), then: n(0), else: n(0)}}}, else: get('marker', x('row'))}}}
  expect(rowAgreementWrittenKeys(m, shape)).toEqual(['i'])
})
test('the row proposer checks plain frame INIT and STEP', () => {
  const {m, law, shape} = fixture(), before = JSON.stringify(m)
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const traces: RowAgreementTrace[] = []
    const until = clock() + 1000, proof = proveRowAgreementCase(m, [law], law, shape, until, (g, ds) => certFor(g, ds, false, 0), {observe: trace => traces.push(trace)})
    expect(proof).toBeDefined()
    expect(traces.map(trace => trace.outcome)).toEqual(['proved'])
    expect(traces[0]!.path.size).toBe(0)
    if (!proof) return
    const packets = countedObligations(m, [law], {[law.name]: proof.instances}, 0)
    for (const p of packets) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
    const step = packets.at(-1)!
    expect(checkMC(step.goal.hyps, step.decls, {...proof.certs[step.goal.name]!, tree: {leaf: []}})).toBe(false)
  }))
  expect(JSON.stringify(m)).toBe(before)
})
test('deferred row cases omit INIT and a separate original INIT proposal checks', () => {
  const {m, law, shape} = fixture(), before = JSON.stringify(m)
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const until = clock() + 1000, request = (g: Parameters<typeof certFor>[0], ds: Parameters<typeof certFor>[1]) => certFor(g, ds, false, 0)
    const deferred = proveRowAgreementCase(m, [law], law, shape, until, request, {deferToComposition: true})
    expect(deferred).toBeDefined()
    expect(deferred?.certs[law.name + ' @start']).toBeUndefined()
    const initial = proposeRowAgreementInitial(m, [law], law, until, request), packet = countedObligations(m, [law], {}, 0)[0]!
    expect(initial).toBeDefined()
    expect(checkMC(packet.goal.hyps, packet.decls, initial!)).toBe(true)
    expect(checkMC(packet.goal.hyps, packet.decls, {...initial!, tree: {leaf: []}})).toBe(false)
    expect(proposeRowAgreementInitial(m, [law], law, clock() - 1, request)).toBeUndefined()
  }))
  expect(JSON.stringify(m)).toBe(before)
})
test('a fixed frame can propose only its own demanded tuple', () => {
  const {m, law, shape} = fixture()
  m.inputs = ['op']; m.assume = all(any(...[0, 1, 2].map(i => same(x('op'), n(i)))), same(x('op'), n(2)))
  const extra: Law = {name: 'irrelevant field fact', forall: 'r', holds: same(get('version', x('r')), n(0))}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const proof = proveRowAgreementCase(m, [law, extra], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {framePremisesOnly: true, operationPath: true})
    expect(proof).toBeDefined()
    expect(proof?.instances[extra.name]).toBeUndefined()
    expect(proof?.instances[law.name]).toEqual([x('a#'), x('b'), x('c')])
    if (proof) for (const p of countedObligations(m, [law, extra], {[law.name]: proof.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
    m.step.maps = {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}
    expect(proveRowAgreementCase(m, [law, extra], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {framePremisesOnly: true, operationPath: true})).toBeUndefined()
  }))
})
test('sparse own-law proposals keep requested source rows but not destination rows', () => {
  const {m, law, shape} = fixture(); m.inputs = ['source', 'destination']
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const options = {sparseOwn: true, ownRows: [x('source')]}
    const proof = proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), options)
    expect(proof).toBeDefined()
    expect(proof?.instances[law.name]).toEqual([x('a#'), x('b'), x('c'), x('source'), x('b'), x('c'), x('a#'), x('source'), x('c')])
    if (proof) for (const p of countedObligations(m, [law], {[law.name]: proof.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
    m.step.maps = {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}
    expect(proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), options)).toBeUndefined()
  }))
})
test('optional linear closure is checked and never authorizes a broken row', () => {
  const {m, law, shape} = fixture(), trivial = {...law, holds: same(n(0), n(0))}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const traces: RowAgreementTrace[] = []
    const proof = proveRowAgreementCase(m, [trivial], trivial, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {fastClosure: true, observe: trace => traces.push(trace)})
    expect(proof).toBeDefined(); expect(traces.some(trace => trace.method === 'linear')).toBe(true)
    for (const p of countedObligations(m, [trivial], {[trivial.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
    m.step = {maps: {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}}
    expect(proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {fastClosure: true})).toBeUndefined()
  }))
})
test('mirrored no-op written-row cases reuse only checked trees', () => {
  const {m, law, shape} = fixture(); m.inputs = ['op', 'i']; m.assume = all(any(...[0, 1, 2].map(value => same(x('op'), n(value)))), same(x('op'), n(1)))
  m.step.maps = {marker: {key: x('i'), value: get('marker', x('i'))}}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const traces: RowAgreementTrace[] = [], proof = proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {symmetryReuse: true, observe: trace => traces.push(trace)})
    expect(proof).toBeDefined(); expect(traces).toHaveLength(9)
    expect(traces.some(trace => trace.method === 'symmetry')).toBe(true)
    for (const p of countedObligations(m, [law], {[law.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
  }))
})
test('written-row diagonal aliases are only ordinary checked splits', () => {
  const {m, law, shape} = fixture(); m.inputs = ['op', 'i']; m.assume = all(any(...[0, 1, 2].map(value => same(x('op'), n(value)))), same(x('op'), n(1)))
  m.step.maps = {marker: {key: x('i'), value: get('marker', x('i'))}}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const traces: RowAgreementTrace[] = [], proof = proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {diagonalAlias: true, symmetryReuse: true, observe: trace => traces.push(trace)})
    expect(proof).toBeDefined()
    expect(traces.some(trace => [...trace.path.values()].some(p => 'a#' in p.lin && 'b' in p.lin))).toBe(true)
    for (const p of countedObligations(m, [law], {[law.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
    m.step.maps = {...m.step.maps, cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}
    expect(proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {diagonalAlias: true, symmetryReuse: true})).toBeUndefined()
  }))
})
test('explicit fixed-operation paths retain checked excluded branches', () => {
  const {m, law, shape} = fixture(); m.inputs = ['op', 'i']; m.assume = all(any(...[0, 1, 2].map(value => same(x('op'), n(value)))), same(x('op'), n(1)))
  m.step.maps = {marker: {key: x('i'), value: get('marker', x('i'))}}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const traces: RowAgreementTrace[] = [], proof = proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {operationPath: true, symmetryReuse: true, observe: trace => traces.push(trace)})
    expect(proof).toBeDefined(); expect(traces).toHaveLength(9)
    expect(traces.every(trace => [...trace.path.values()].some(p => 'op' in p.lin))).toBe(true)
    for (const p of countedObligations(m, [law], {[law.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
  }))
})
test('an anchored own-law pool keeps only the demanded pair for a plain frame', () => {
  const {m, law, shape} = fixture()
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const proof = proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {sparseOwn: true, symmetryReuse: true})
    expect(proof).toBeDefined(); expect(proof!.instances[law.name]).toHaveLength(3)
    for (const p of countedObligations(m, [law], {[law.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
    m.step = {maps: {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}}
    expect(proveRowAgreementCase(m, [law], law, shape, clock() + 1000, (g, ds) => certFor(g, ds, false, 0), {sparseOwn: true, symmetryReuse: true})).toBeUndefined()
  }))
})
test('an optional premise pool keeps target rows and explicit seeds, not incidental reads', () => {
  const {m, law, shape} = fixture(); m.inputs = ['incidental']
  m.step.maps = {version: {key: x('incidental'), value: get('version', x('incidental'))}}
  const helper: Law = {name: 'marker bound', forall: 'r', holds: {op: '<=', a: get('marker', x('r')), b: n(1)}}
  const seed = {[helper.name]: [x('incidental')]}, before = JSON.stringify(seed)
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const request = (g: Parameters<typeof certFor>[0], ds: Parameters<typeof certFor>[1]) => certFor(g, ds, false, 0)
    const options = {sparseOwn: true, premiseRows: [], seedInstances: seed}
    const proof = proveRowAgreementCase(m, [law, helper], law, shape, clock() + 1500, request, options)
    expect(proof).toBeDefined()
    expect(proof!.instances[law.name]).toEqual([x('a#'), x('b'), x('c')])
    expect(proof!.instances[helper.name]).toEqual([x('a#'), x('b'), x('incidental')])
    expect(JSON.stringify(seed)).toBe(before)
    for (const p of countedObligations(m, [law, helper], {[law.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
    const defaultGoals: Parameters<typeof certFor>[0][] = []
    proveRowAgreementCase(m, [law, helper], law, shape, clock() + 1500, (g, ds) => {defaultGoals.push(g); return request(g, ds)}, {sparseOwn: true})
    const defaults = {[law.name]: [x('a#'), x('b'), x('c'), x('incidental'), x('b'), x('c'), x('a#'), x('incidental'), x('c')], [helper.name]: [x('a#'), x('b'), x('incidental')]}
    expect(defaultGoals[0]?.hyps).toEqual(countedObligations(m, [law, helper], {[law.name]: defaults}, 0).at(-1)!.goal.hyps)
    m.step.maps = {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}
    expect(proveRowAgreementCase(m, [law, helper], law, shape, clock() + 1000, request, options)).toBeUndefined()
  }))
})
test('explicit premise mode does not silently seed unrelated family laws', () => {
  const {m, law, shape} = fixture(), unrelated: Law = {name: 'unrelated marker', forall: 'q', holds: same(get('marker', x('q')), n(1))}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const proof = proveRowAgreementCase(m, [law, unrelated], law, shape, clock() + 1000,
      (g, ds) => certFor(g, ds, false, 0), {onlySeededPremises: true})
    expect(proof).toBeDefined()
    expect(proof!.instances[unrelated.name]).toBeUndefined()
    for (const p of countedObligations(m, [law, unrelated], {[law.name]: proof!.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, proof!.certs[p.goal.name]!)).toBe(true)
    m.step.maps = {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}
    expect(proveRowAgreementCase(m, [law, unrelated], law, shape, clock() + 1000,
      (g, ds) => certFor(g, ds, false, 0), {onlySeededPremises: true})).toBeUndefined()
  }), true)
})
test('explicit PRE instances are recorded without mutating the seed', () => {
  const {m, law, shape} = fixture(), seed = {[law.name]: [x('b'), x('a'), x('c')]}, before = JSON.stringify(seed)
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const proof = proveRowAgreementCase(m, [law], law, shape, clock() + 4000, (g, ds) => certFor(g, ds, false, 0), {seedInstances: seed, witnessFlags: true})
    expect(proof).toBeDefined(); expect(JSON.stringify(seed)).toBe(before)
    expect(proof!.instances[law.name]).toEqual(expect.arrayContaining(seed[law.name]!))
    for (const packet of countedObligations(m, [law], {[law.name]: proof!.instances}, 0)) expect(checkMC(packet.goal.hyps, packet.decls, proof!.certs[packet.goal.name]!)).toBe(true)
  }))
})
test('an unchecked shape cannot make a broken row write inductive', () => {
  const {m, law, shape} = fixture(); m.step = {maps: {cells: {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}}}
  counted(fullRate, () => withWall(performance.now() + 4000, () => {
    const until = clock() + 1000, traces: RowAgreementTrace[] = []
    expect(proveRowAgreementCase(m, [law], law, shape, until, (g, ds) => certFor(g, ds, false, 0), {observe: trace => traces.push(trace)})).toBeUndefined()
    expect(traces.length).toBeGreaterThan(0)
    expect(traces.every(trace => trace.outcome !== 'proved')).toBe(true)
  }))
})
