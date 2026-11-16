// Concrete source conformance, not a symbolic proof or a new acceptance path.
import {expect, test} from 'bun:test'
import {compileC, cpair, interpret, loadJs, type Machine, type State} from '../../core/machine.ts'
import {allowed} from '../../core/watch.ts'
import {validateRigidInstance} from './rigid-instance.ts'
import {rigidQuorumSignature} from './rigid-minimal.ts'
import {rigidNaive} from './rigid-naive.ts'

type Sizes = {nodes: number, quorums: number, values: number}
type Request = {action: number, node: number, quorum: number, value: number}
type SourceState = {vote: number[][], decide: number[][], decision: number[]}
const range = (n: number) => Array.from({length: n}, (_, i) => i)
const matrix = (n: number, m: number) => range(n).map(() => range(m).map(() => 0))
const sourceInit = (p: Sizes): SourceState => ({vote: matrix(p.nodes, p.values), decide: matrix(p.quorums, p.values), decision: range(p.values).map(() => 0)})
// This interpreter uses arrays and loops only, not C/E, tuple encoding, flags,
// lowering, ghost state or the implementation's evaluator.
function sourceEnabled(p: Sizes, member: number[][], s: SourceState, r: Request, revote = false): boolean {
  if (r.value < 0 || r.value >= p.values) return false
  if (r.action === 0) return r.node >= 0 && r.node < p.nodes && (revote || s.vote[r.node]!.every(x => x === 0))
  if (r.action === 1) return r.quorum >= 0 && r.quorum < p.quorums && range(p.nodes).every(n => member[n]![r.quorum] === 0 || s.vote[n]![r.value] === 1)
  if (r.action === 2) return r.quorum >= 0 && r.quorum < p.quorums && s.decide[r.quorum]![r.value] === 1
  return false
}
function sourceStep(p: Sizes, member: number[][], s: SourceState, r: Request, revote = false): SourceState {
  const next = structuredClone(s)
  if (!sourceEnabled(p, member, s, r, revote)) return next
  if (r.action === 0) next.vote[r.node]![r.value] = 1
  if (r.action === 1) next.decide[r.quorum]![r.value] = 1
  if (r.action === 2) next.decision[r.value] = 1
  return next
}
function projection(m: Machine, s: State, p: Sizes): SourceState {
  const cell = (name: string, key: number) => s.maps[name]!.get(key) ?? s.defaults?.[name] ?? m.maps![name]!
  return {vote: range(p.nodes).map(n => range(p.values).map(v => cell('vote', cpair(n, v)))), decide: range(p.quorums).map(q => range(p.values).map(v => cell('decide', cpair(q, v)))), decision: range(p.values).map(v => cell('decision', v))}
}
// Compiled exposes step(), not interpret().queries(). Compile the actual guard
// and flags independently instead of pretending the two runtime APIs match.
function compileEnabled(m: Machine, params: Readonly<Record<string, number>>) {
  if (m.leasts || m.history) throw Error('this source fixture has no queries or history')
  const flags = Object.entries(m.step.flags ?? {}).map(([name, c]) => ({name, holds: compileC(c, m)}))
  const assumption = m.assume ? compileC(m.assume, m) : () => true
  return (s: State, r: Request): boolean => {
    const env: Record<string, number> = {...params, ...r}
    for (const {name, holds} of flags) env[`?${name}`] = holds(env, s) ? 1 : 0
    return assumption(env, s)
  }
}
function boundCase(p: Sizes, member: number[][]) {
  const instance = validateRigidInstance(rigidQuorumSignature, JSON.stringify({params: p, tables: {member: member.flat()}}), () => {})
  const port = rigidNaive(), bound = port.lowered.bind(instance)
  return {port, bound, instance, cpu: interpret(bound.machine), js: loadJs(bound.machine), jsEnabled: compileEnabled(bound.machine, bound.params)}
}
function sourceInvariants(p: Sizes, member: number[][], s: SourceState): void {
  expect(s.decision.filter(x => x === 1).length).toBeLessThanOrEqual(1)
  for (const row of s.vote) expect(row.filter(x => x === 1).length).toBeLessThanOrEqual(1)
  for (const q of range(p.quorums)) for (const v of range(p.values)) if (s.decide[q]![v] === 1) {
    expect(range(p.nodes).every(n => member[n]![q] === 0 || s.vote[n]![v] === 1)).toBe(true)
  }
  for (const v of range(p.values)) if (s.decision[v] === 1) expect(range(p.quorums).some(q => s.decide[q]![v] === 1)).toBe(true)
}
function allRequests(p: Sizes): Request[] {
  // Includes one out-of-range index per sort and the invalid action 3. Unused
  // request coordinates must remain irrelevant exactly as in the Ivy source.
  return range(4).flatMap(action => range(p.nodes + 1).flatMap(node => range(p.quorums + 1).flatMap(quorum => range(p.values + 1).map(value => ({action, node, quorum, value})))))
}
function checkTrace(p: Sizes, member: number[][], requests: Request[]): SourceState {
  const {bound, cpu, js, jsEnabled} = boundCase(p, member)
  let ref = sourceInit(p), si = bound.init(), sj = js.init(bound.params)
  for (const r of requests) {
    const enabled = sourceEnabled(p, member, ref, r)
    expect(allowed(bound.machine, cpu, bound.params, si, r)).toBe(enabled)
    expect(jsEnabled(sj, r)).toBe(enabled)
    if (!enabled) {
      expect(() => bound.step(si, r)).toThrow(RangeError)
      expect(() => js.step(bound.params, js.fork(sj), r)).toThrow(RangeError)
      continue // a disabled source action is absent, not a stuttering step
    }
    ref = sourceStep(p, member, ref, r); si = bound.step(si, r); sj = js.step(bound.params, sj, r)
    expect(projection(bound.machine, si, p)).toEqual(ref)
    expect(projection(bound.machine, sj, p)).toEqual(ref)
    sourceInvariants(p, member, ref)
  }
  return ref
}

test('all reachable 2x2x2 states and request transitions match independent Ivy and both runtimes', () => {
  const p = {nodes: 2, quorums: 2, values: 2}, member = [[1, 1], [0, 1]], {port, bound, cpu, js, jsEnabled} = boundCase(p, member)
  expect(Object.keys(bound.machine.maps!)).toEqual(['vote', 'decide', 'decision'])
  expect(bound.machine.maps!.learnedQuorum).toBeUndefined()
  expect(port.lowered.abstractMachine.counts).toBeUndefined()
  const requests = allRequests(p), initial = sourceInit(p)
  const queue = [{ref: initial, si: bound.init(), sj: js.init(bound.params)}], seen = new Set([JSON.stringify(initial)])
  let transitions = 0
  for (let i = 0; i < queue.length; i++) {
    const {ref, si, sj} = queue[i]!
    sourceInvariants(p, member, ref)
    for (const r of requests) {
      transitions++
      const enabled = sourceEnabled(p, member, ref, r)
      expect(allowed(bound.machine, cpu, bound.params, si, r)).toBe(enabled)
      expect(jsEnabled(sj, r)).toBe(enabled)
      if (!enabled) {
        expect(() => bound.step(si, r)).toThrow(RangeError)
        expect(() => js.step(bound.params, js.fork(sj), r)).toThrow(RangeError)
        continue
      }
      // Compiled.step consumes its state; each BFS edge needs its own fork.
      const nr = sourceStep(p, member, ref, r), ni = bound.step(si, r), nj = js.step(bound.params, js.fork(sj), r)
      expect(projection(bound.machine, ni, p)).toEqual(nr)
      expect(projection(bound.machine, nj, p)).toEqual(nr)
      const key = JSON.stringify(nr)
      if (!seen.has(key)) { seen.add(key); queue.push({ref: nr, si: ni, sj: nj}) }
    }
    expect(seen.size).toBeLessThanOrEqual(3 ** p.nodes * 2 ** (p.quorums * p.values + p.values))
  }
  expect(seen.size).toBeGreaterThan(10)
  console.log(JSON.stringify({concreteSourceConformance: true, sizes: p, states: seen.size, requestsPerState: requests.length, transitions, symbolicProof: false}))
}, 120_000)

test('non-majority intersecting quorums preserve all three original relations', () => {
  const p = {nodes: 4, quorums: 2, values: 2}, member = [[1, 1], [1, 0], [0, 1], [0, 0]]
  expect(member.filter(row => row[0]).length * 2).toBe(p.nodes)
  const r = (action: number, node: number, quorum: number, value: number): Request => ({action, node, quorum, value})
  const final = checkTrace(p, member, [r(0, 0, 0, 1), r(1, 0, 0, 1), r(0, 1, 0, 1), r(1, 0, 0, 1), r(2, 0, 0, 1), r(0, 2, 0, 1), r(1, 0, 1, 1), r(2, 0, 1, 1), r(0, 0, 0, 0), r(0, 3, 0, 0), r(1, 0, 1, 0)])
  expect(final.decision).toEqual([0, 1]); expect(final.decide).toEqual([[0, 1], [0, 1]])
})

test('node and value coordinates above 64 and duplicate-extension quorum names work', () => {
  const p = {nodes: 66, quorums: 2, values: 66}, member = range(p.nodes).map(n => [Number(n >= 64), Number(n >= 64)])
  expect(boundCase(p, member).instance.witness('intersection', [0, 1])).toBe(64)
  const r = (action: number, node: number, quorum: number, value: number): Request => ({action, node, quorum, value})
  const final = checkTrace(p, member, [r(0, 64, 0, 65), r(1, 0, 1, 65), r(0, 65, 0, 65), r(1, 0, 1, 65), r(2, 0, 1, 65), r(0, 65, 0, 64), r(1, 0, 0, 65), r(2, 0, 0, 65)])
  expect(final.vote[65]![64]).toBe(0); expect(final.vote[65]![65]).toBe(1)
  expect(final.decision[65]).toBe(1)
})

test('empty sorts keep the source semantics, without a blanket inhabitance assumption', () => {
  for (const p of [{nodes: 0, quorums: 0, values: 2}, {nodes: 3, quorums: 0, values: 2}, {nodes: 2, quorums: 1, values: 0}]) {
    const member = range(p.nodes).map(() => range(p.quorums).map(() => 1))
    checkTrace(p, member, allRequests(p))
  }
  expect(() => boundCase({nodes: 0, quorums: 1, values: 2}, [])).toThrow('no witness')
})

test('dropping intersection admits a concrete bad source trace, rejected by the normal API', () => {
  const p = {nodes: 2, quorums: 2, values: 2}, member = [[1, 0], [0, 1]]
  expect(() => boundCase(p, member)).toThrow('no witness at (0, 1)')
  let s = sourceInit(p)
  for (const [action, node, quorum, value] of [[0, 0, 0, 0], [0, 1, 0, 1], [1, 0, 0, 0], [1, 0, 1, 1], [2, 0, 0, 0], [2, 0, 1, 1]]) {
    const r = {action: action!, node: node!, quorum: quorum!, value: value!}
    expect(sourceEnabled(p, member, s, r)).toBe(true); s = sourceStep(p, member, s, r)
  }
  expect(s.decision).toEqual([1, 1])
})

test('removing the no-prior-vote guard has the concrete bad trace in both runtimes', () => {
  const p = {nodes: 1, quorums: 1, values: 2}, member = [[1]], {bound} = boundCase(p, member)
  const mutant = structuredClone(bound.machine)
  mutant.step.flags!.unvoted = {op: '=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const compiledAllowed = compileEnabled(mutant, bound.params)
  for (const cpu of [interpret(mutant), loadJs(mutant)]) {
    let s = cpu.init(bound.params), ref = sourceInit(p)
    for (const value of [0, 1]) for (const action of [0, 1, 2]) {
      const r = {action, node: 0, quorum: 0, value}
      expect(compiledAllowed(s, r)).toBe(true)
      ref = sourceStep(p, member, ref, r, true); s = cpu.step(bound.params, s, r)
      expect(projection(mutant, s, p)).toEqual(ref)
    }
    expect(ref.decision).toEqual([1, 1])
  }
})

test('changing membership between steps breaks the source contract even if each table intersects', () => {
  const p = {nodes: 2, quorums: 1, values: 2}, first = [[1], [0]], later = [[0], [1]]
  boundCase(p, first); boundCase(p, later) // each table independently satisfies intersection
  let s = sourceInit(p)
  for (const value of [0, 1]) for (const action of [0, 1, 2]) {
    const r = {action, node: value, quorum: 0, value}, member = value === 0 ? first : later
    expect(sourceEnabled(p, member, s, r)).toBe(true); s = sourceStep(p, member, s, r)
  }
  expect(s.decision).toEqual([1, 1]) // explicitly invalid: not one fixed interpretation
})
