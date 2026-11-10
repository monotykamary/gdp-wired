import {expect, test} from 'bun:test'
import {type Machine, any, get, ite, less, n, not, same, x} from './machine.ts'
import {seedCountWitnessFlags} from './count-witness-flags.ts'
import {checkMC, mcGoal, substC} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'

test('selected count witnesses receive relevant universal flags, without recursive count reads', () => {
  const q = same(get('Q', x('k')), n(1)), a = same(get('A', x('k')), n(1)), predicate = any(not(q), a)
  const machine: Machine = {name: 'subset', params: [], inputs: [], state: {}, maps: {Q: 0, A: 0, Other: 0}, counts: {
    stored: {j: 'j', key: 'k', below: n(4), body: ite(a, n(1), n(0))},
  }, step: {flags: {
    eligible: {op: 'all', key: 'k', c: predicate},
    unrelated: {op: 'all', key: 'k', c: same(get('Other', x('k')), n(0))},
    targetOnly: {op: 'all', key: 'k', c: same(get('A', x('k')), n(1))},
    recursive: {op: 'all', key: 'k', c: same(get('stored', x('k')), n(0))},
  }}}
  const decls = [
    {map: 'Requested', j: 'unused', key: 'k', below: n(4), body: ite(q, n(1), n(0))},
    {map: 'Allowed', j: 'unused', key: 'k', below: n(4), body: ite(a, n(1), n(0))},
  ]
  const cert = {reads: [['rq', 'Requested', n(0)], ['ra', 'Allowed', n(0)]] as [string,string,ReturnType<typeof n>][], insts: [{wit: 'member', below: n(4), terms: [[1,'rq'],[-1,'ra']] as [number,string][], unit: 0}]}
  const at = {'?eligible': [x('previous')]}
  const seeded = seedCountWitnessFlags(machine, at, [{decls, cert}])
  expect(at['?eligible']).toEqual([x('previous')])
  expect(seeded['?eligible']).toEqual([x('previous'),x('member')])
  expect(seeded['?unrelated']).toBeUndefined()
  expect(seeded['?recursive']).toBeUndefined()
  expect(seedCountWitnessFlags(machine, seeded, [{decls, cert}])).toBe(seeded)
  expect(seeded['?targetOnly']).toEqual([x('member')])
  const preferred=seedCountWitnessFlags({...machine,inputMaps:['Q']},at,[{decls,cert}],true)
  expect(preferred['?eligible']).toEqual([x('previous'),x('member')])
  expect(preferred['?targetOnly']).toBeUndefined()
  const onlyCarried=seedCountWitnessFlags({...machine,inputMaps:['Q']},at,[{decls,cert:{...cert,insts:[{...cert.insts[0]!,terms:[[1,'ra']]}]}}],true,{carriedOnly:true})
  expect(onlyCarried).toBe(at)
  const noLiveReads=seedCountWitnessFlags(machine,at,[{decls,cert}],false,{dependencies:()=>new Set()})
  expect(noLiveReads).toBe(at)
  const hyps = [substC(predicate, {vars:{k:x('member')},maps:{},flags:{}}), less(get('Allowed', n(0)), get('Requested', n(0)))]
  const goal = mcGoal(hyps, decls, cert)!
  const result = grow({name:'subset witness',hyps:goal.hyps}, new Map(), {nodes:0,until:clock()+1500})
  expect('tree' in result).toBe(true)
  if ('tree' in result) expect(checkMC(hyps,decls,{...cert,tree:result.tree})).toBe(true)
})
