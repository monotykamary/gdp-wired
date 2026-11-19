// Shared by the fast unit shard and the Node release admission job.
import assert from 'node:assert/strict'
import {n, same, x, type Law, type Machine} from '../../core/machine.ts'
import {attachNativeLaw, attachSource, bindSourceMachine} from '../../core/source-check.ts'
import {items as raft, raftTally} from '../../research/realworld/items/dist-etcd-raft.ts'
import {items as tiger} from '../../research/realworld/items/ledgerpay-tigerbeetle.ts'
import {invariantInput} from '../../research/realworld/lib.ts'
import {proveLeanAggregate} from './index.ts'
import {admitAggregateSource} from './source.ts'

export function corpusInput(index: 0 | 1 | 2 | 3): [Machine, Law] {
  const item = index < 2 ? raft.find(i => i.id === 'distributed/etcd-raft/tally') : tiger.find(i => i.id === 'ledger/tigerbeetle/transfers')
  const row = item?.laws[index % 2]
  assert(row?.form === 'invariant')
  const args = invariantInput(row)
  assert(args, 'the release job must use the original corpus invariant')
  return [args[0].machine, args[1]]
}

export async function checkAdmissionControls(): Promise<string[]> {
  const [machine, law] = corpusInput(0)
  const falseLaw: Law = {...law, holds: same(n(0), n(1))}
  const names: string[] = []
  let calls = 0
  const called = () => { calls++ }
  const refused = async (name: string, m: Machine, l: Law, detail: RegExp) => {
    const result = await proveLeanAggregate(m, l)
    assert(result.kind === 'not-checked' && result.reason === 'unsupported', name)
    assert.match(result.detail, detail, name)
    assert(!('receipt' in result) && !('checked' in result) && !('proven' in result), name)
    assert.equal(calls, 0, name)
    names.push(name)
  }

  // Admission alone must keep the exact body/binder for all four corpus laws.
  for (const index of [0, 1, 2, 3] as const) {
    const pair = corpusInput(index)
    assert.equal(admitAggregateSource(...pair), JSON.stringify(pair))
  }
  assert.equal(admitAggregateSource(machine, falseLaw), JSON.stringify([machine, falseLaw]))
  const passive = Object.assign(Object.create(null) as Machine, machine)
  assert.equal(admitAggregateSource(Object.freeze(passive), law), JSON.stringify([machine, law]))

  const hookedLaw = {...falseLaw, toJSON: () => { called(); return law }}
  await refused('law-toJSON', machine, hookedLaw, /source property/)
  const badMachine = {...machine, params: ['n', 'n']}
  const hookedMachine = {...badMachine, toJSON: () => { called(); return machine }}
  await refused('machine-toJSON', hookedMachine, law, /source property/)
  const inherited = Object.setPrototypeOf({...falseLaw}, {toJSON: () => { called(); return law }}) as Law
  await refused('inherited-toJSON', machine, inherited, /prototype/)
  const nested = {...falseLaw, holds: Object.defineProperty({...falseLaw.holds}, 'toJSON', {value: () => { called(); return law.holds }})}
  await refused('nested-toJSON', machine, nested, /source property/)
  const getter = Object.defineProperty({...falseLaw}, 'holds', {get: () => { called(); return law.holds }})
  await refused('law-accessor', machine, getter, /own data/)
  const inputs = Object.defineProperty([...machine.inputs], '0', {get: () => { called(); return machine.inputs[0] }})
  await refused('array-accessor', {...machine, inputs}, law, /own data/)
  const proxy = new Proxy(machine, {getOwnPropertyDescriptor: () => { called(); return undefined }})
  await refused('root-proxy', proxy, law, /passive data/)
  const proxyTerm = new Proxy(law.holds, {ownKeys: () => { called(); return [] }})
  await refused('nested-proxy', machine, {...law, holds: proxyTerm}, /passive JSON data/)
  const sparse = [...machine.inputs]
  assert(Reflect.deleteProperty(sparse, '0'))
  await refused('sparse-array', {...machine, inputs: sparse}, law, /dense/)
  const decorated = Object.assign([...machine.inputs], {extra: 0})
  await refused('array-extra-data', {...machine, inputs: decorated}, law, /extra properties/)
  const hiddenMap = Object.defineProperty({...machine.maps}, 'hidden', {value: 0})
  await refused('nonenumerable-data', {...machine, maps: hiddenMap}, law, /own data/)
  await refused('explicit-undefined', {...machine, pre: undefined} as unknown as Machine, law, /omit absent optional fields/)
  const cycle = {...machine}; Object.assign(cycle, {loop: cycle})
  await refused('cyclic-data', cycle, law, /cyclic/)

  const extracted = raftTally()
  attachSource(extracted, {}, [])
  const markedMachine = structuredClone(machine)
  bindSourceMachine(extracted, markedMachine)
  assert.equal(JSON.stringify(markedMachine), JSON.stringify(machine))
  await refused('marked-machine-without-journal', markedMachine, law, /Source-bound/)
  const markedLaw = {...law}
  attachNativeLaw(extracted, markedLaw, law.name, undefined, () => { called(); return true })
  assert.equal(JSON.stringify(markedLaw), JSON.stringify(law))
  await refused('marked-law-from-another-rule', machine, markedLaw, /Source-bound/)

  await refused('duplicate-parameter', badMachine, law, /declares n twice/)
  await refused('parameter-state-collision', {...machine, params: ['n', 'yes']}, law, /declares yes twice/)
  await refused('request-in-invariant', machine, {...law, holds: same(x('id'), n(0))}, /id/)
  const write = machine.step.maps?.V
  assert(write && 'each' in write)
  await refused('illegal-write-binder', {...machine, step: {...machine.step, maps: {V: {...write, each: 'id'}}}}, law, /key id is already a name/)
  const [weighted, limit] = corpusInput(2)
  await refused('weighted-source-scope', {...weighted, params: [...weighted.params, weighted.params[0]!]}, limit, /declares .* twice/)
  return names
}
