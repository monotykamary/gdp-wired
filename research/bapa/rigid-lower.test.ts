import {test, expect} from 'bun:test'
import {argsKey, compileC, evalE, fastStep, fnCall, interpret, loadJs, type C, type E, type Law, type Machine} from '../../core/machine.ts'
import {scope} from '../../kernel/kernel.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {holdsAt} from '../../core/exists.ts'
import {watch} from '../../core/watch.ts'
import {finiteEvaluator} from '../../core/finite-houdini.ts'
import {bmcFits} from '../../core/bmc.ts'
import {domainStep} from '../../core/infer.ts'
import {requestQuotient} from '../../core/request-quotient.ts'
import {validateRigidInstance} from './rigid-instance.ts'
import {lowerRigid} from './rigid-lower.ts'
import {rigidMinimal, rigidMinimalGivenZero, rigidMinimalBase, rigidMinimalLaw, rigidQuorumSignature} from './rigid-minimal.ts'
const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const data = (nodes = 4, quorums = 2, member = [1, 1, 1, 0, 0, 1, 0, 0], values = 0) => JSON.stringify({params: {nodes, quorums, values}, tables: {member}})
const valid = (text = data()) => validateRigidInstance(rigidQuorumSignature, text, () => {})

test('diagnostic minimal law closes with a GIVEN zero-tuple axiom seed, not found', () => {
  const p = rigidMinimalGivenZero()
  expect(proveLaws(p.abstractMachine, [rigidMinimalLaw])).toMatchObject({proven: true, checked: true})
  expect(p.abstractMachine.maps).toBeUndefined()
  expect(p.instancePrecondition.axioms[0]!.exists.sort).toBe('Node')
})
test('the minimal claim is not accepted without its source axiom facts', () => {
  const p = rigidMinimal(), m = {...p.abstractMachine, facts: p.abstractMachine.facts!.filter(f => !f.name.includes('axiom'))}
  expect(proveLaws(m, [rigidMinimalLaw]).proven).toBe(false)
})
test('binding supplies immutable functions but retains symbolic abstract sizes', () => {
  const p = rigidMinimal(), b = p.bind(valid())
  expect(fnCall(b.machine.fns!.member!, [0, 0])).toBe(1)
  expect(fnCall(b.machine.fns!.member!, [3, 0])).toBe(0)
  expect(fnCall(b.machine.fns![p.auxiliaries.intersection!]!, [0, 1])).toBe(0)
  expect(b.step(b.init(), {})).toEqual(b.init())
  expect(p.abstractMachine.pre).toBeUndefined()
  expect(() => { (b.params as any).nodes = 99 }).toThrow()
  expect(() => p.bind(valid(), {nodes: 99})).toThrow('cannot rebind')
})
test('binding rejects lookalikes before calling any user-supplied lookup', () => {
  const p = rigidMinimal(), instance = valid()
  let called = false
  const fake = Object.assign({}, instance, {read: () => { called = true; return 1 }, witness: () => { called = true; return 0 }})
  expect(() => p.bind(fake as any)).toThrow('returned by validation')
  expect(called).toBe(false)
  expect(() => p.bind(Object.create(Object.getPrototypeOf(instance)))).toThrow('returned by validation')
})
test('a different source precondition cannot be substituted at binding', () => {
  const s = structuredClone(rigidQuorumSignature); (s.axioms as any[]).splice(0)
  const unrelated = validateRigidInstance(s, data(), () => {})
  expect(() => rigidMinimal().bind(unrelated)).toThrow('different precondition')
})
test('rigid symbols cannot collide with mutable or carried maps', () => {
  for (const patch of [{maps: {member: 0}}, {inputMaps: ['member']}]) expect(() => lowerRigid({...rigidMinimalBase, ...patch}, rigidQuorumSignature)).toThrow('collision')
  expect(() => lowerRigid({...rigidMinimalBase, step: {maps: {member: {key: k(0), value: k(0)}}}}, rigidQuorumSignature)).toThrow()
})
test('two different marked sorts, a rigid function and native tuple reads work in both CPU runtimes', () => {
  const member: E = {op: 'get', map: 'member', key: argsKey([v('n'), v('quorum')])}
  const votes = (node: E, value: E): E => ({op: 'get', map: 'Votes', key: {op: 'tup', a: node, b: value}})
  const finite = (sort: string, key: string, size: string, body: C): C => ({op: 'all', key, finite: sort, c: {op: 'or', xs: [{op: 'not', x: {op: '<', a: v(key), b: v(size)}}, body]}})
  const base: Machine = {...rigidMinimalBase, name: 'multi-sort rigid/tuple guard', inputs: ['node', 'quorum', 'value'], maps: {Votes: 0}, state: {collect: k(0), cast: k(0)}, step: {
    flags: {
      collected: finite('Node', 'n', 'nodes', {op: 'or', xs: [{op: 'not', x: {op: '=', a: member, b: k(1)}}, {op: '=', a: votes(v('n'), v('value')), b: k(1)}]}),
      unvoted: finite('Value', 'w', 'values', {op: '=', a: votes(v('node'), v('w')), b: k(0)}),
    }, state: {collect: {op: 'if', c: {op: 'flag', name: 'collected'}, then: k(1), else: k(0)}, cast: {op: 'if', c: {op: 'flag', name: 'unvoted'}, then: k(1), else: k(0)}},
  }}
  const table = Array.from({length: 140}, (_, i) => Number(Math.floor(i / 2) === 17 || Math.floor(i / 2) === 35))
  const p = lowerRigid(base, rigidQuorumSignature), b = p.bind(valid(data(70, 2, table, 65)))
  scope(b.machine)
  const request = {node: 17, quorum: 0, value: 0}, empty = b.init(), js = loadJs(b.machine)
  const env = {...b.params, ...request}
  expect(compileC(base.step.flags!.collected!, b.machine)(env, empty)).toBe(false)
  expect(compileC(base.step.flags!.unvoted!, b.machine)(env, empty)).toBe(true)
  expect(fastStep(b.machine)).toBeUndefined()
  expect(domainStep(b.machine)).toBeUndefined()
  expect(requestQuotient(b.machine, [request])).toBeUndefined()
  const guardedNode = finite('Node', 'n', 'nodes', {op: 'or', xs: [
    {op: 'not', x: {op: '=', a: {op: 'get', map: 'member', key: argsKey([v('n'), k(0)])}, b: k(1)}},
    {op: '=', a: votes(v('n'), k(0)), b: k(1)},
  ]}) as Extract<C, {op: 'all'}>
  const guardedValue = finite('Value', 'w', 'values', {op: '=', a: votes(k(17), v('w')), b: k(0)}) as Extract<C, {op: 'all'}>
  const nodeLaw: Law = {name: 'all quorum nodes voted', forall: 'n', finite: 'Node', holds: guardedNode.c}
  const valueLaw: Law = {name: 'node has no vote', forall: 'w', finite: 'Value', holds: guardedValue.c}
  scope(b.machine, [nodeLaw, valueLaw])
  expect(holdsAt(b.machine, nodeLaw, b.params, empty, 4)).toBe(false)
  expect(watch(b.machine, interpret(b.machine), nodeLaw, b.params, 4).start(empty)).toBe(false)
  expect(bmcFits(b.machine, [nodeLaw, valueLaw])).toBe(false)
  expect(finiteEvaluator(b.machine)(nodeLaw, b.params, empty)).toBeUndefined()
  const laterValue = b.init()
  laterValue.maps.Votes!.set(evalE({op: 'tup', a: k(17), b: k(42)}, b.params, laterValue, b.machine), 1)
  expect(holdsAt(b.machine, valueLaw, b.params, laterValue, 4)).toBe(false)
  expect(watch(b.machine, interpret(b.machine), valueLaw, b.params, 4).start(laterValue)).toBe(false)
  expect(b.step(empty, request).scalars).toEqual({collect: 0, cast: 1})
  expect(js.step(b.params, js.init(b.params), request).scalars).toEqual({collect: 0, cast: 1})
  const full = b.init()
  for (const node of [17, 35]) full.maps.Votes!.set(evalE({op: 'tup', a: k(node), b: k(0)}, b.params, full, b.machine), 1)
  expect(b.step(full, request).scalars).toEqual({collect: 1, cast: 0})
  expect(js.step(b.params, structuredClone(full), request).scalars).toEqual({collect: 1, cast: 0})
})
