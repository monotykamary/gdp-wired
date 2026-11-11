import {expect,test} from 'bun:test'
import {type C,type E,type Machine,all,any,atMost,get,ite,less,minus,n,not,plus,same,times,x} from './machine.ts'
import {quorumLaws,quorumLawProvenance} from './quorum-laws.ts'
import {discoverLiftedCountGuard,discoverLiftedCountOperation} from './count-lifted-shape.ts'
import {discoverLiftedCountPrerequisites} from './count-lifted-prerequisite.ts'
import {proveLiftedCountIncrement} from './count-lifted-increment.ts'
import {restrictedCounts} from './count-restrictions.ts'
import {clock,counted,fullRate} from '../kernel/prove.ts'
const bit = (c: C) => ite(c, n(1), n(0))
const fixture = (base = 8): Machine => {
  const cell = (r: E, k: E) => same(get('Rows', plus(times(base, r), k)), n(1)), member = (k: E) => atMost(n(1), get('Proposal', k))
  const cnt = (body: (k: E) => C) => ({j: 'j', key: 'k', below: x('size'), body: bit(body(x('k')))})
  const read = (name: string) => get(name, n(0))
  return {name: 'row-election fixture', params: ['size'], inputs: ['row', 'left', 'right'], state: {}, maps: {Rows: 0, Epoch: 0, Written: 0, Version: 0}, inputMaps: ['Proposal'],
    counts: {rowCount: cnt(k => cell(x('row'), k)), members: cnt(member), diff: cnt(k => all(cell(x('row'), k), not(member(k)))), reverse: cnt(k => all(member(k), not(cell(x('row'), k)))), meet: cnt(k => all(cell(x('row'), k), member(k)))},
    assume: all(less(x('row'), x('size')), less(read('rowCount'), times(2, read('members'))), atMost(times(2, x('left')), read('rowCount')), less(read('rowCount'), plus(times(2, x('left')), n(2))), atMost(times(2, x('right')), read('members')), less(read('members'), plus(times(2, x('right')), n(2)))),
    step: {flags: {
      eligible: {op: 'all', key: 'voter', c: any(not(member(x('voter'))), all(less(get('Epoch', x('voter')), plus(get('Epoch', x('row')), n(1))), atMost(get('Version', x('voter')), get('Version', x('row')))))},
      elect: {op: 'flag', name: 'eligible'},
      change: less(read('meet'), plus(minus(plus(x('left'), n(1)), read('diff')), minus(plus(x('right'), n(1)), read('reverse')))),
    }, maps: {
      Written: {each: 'z', value: ite(all({op: 'flag', name: 'elect'}, same(x('z'), x('row'))), plus(get('Epoch', x('row')), n(1)), get('Written', x('z')))},
      Rows: {each: 'z', value: ite(all({op: 'flag', name: 'change'}, atMost(times(base, x('row')), x('z')), less(x('z'), plus(times(base, x('row')), n(base)))), bit(member(minus(x('z'), times(base, x('row'))))), get('Rows', x('z')))},
    }},
  }
}
const incrementFixture=()=>{
 const original=fixture();original.inputs.push('operation')
 original.pre=all(atMost(n(1),x('size')),atMost(x('size'),n(8)))
 original.assume=all(original.assume!,any(same(x('operation'),n(4)),same(x('operation'),n(7)),same(x('operation'),n(11))),same(x('operation'),n(4)))
 original.step.flags!.elect=all(same(x('operation'),n(4)),original.step.flags!.elect!,atMost(n(0),get('Proposal',n(0))))
 original.step.flags!.change=all(same(x('operation'),n(7)),original.step.flags!.change!)
 const g=quorumLaws(original,true),m={...original,counts:{...original.counts,...g.counts}},law=g.laws.find(candidate=>quorumLawProvenance(candidate)?.disabled)!
 const shape=discoverLiftedCountGuard(m,law,g.laws)!,matches=discoverLiftedCountPrerequisites(m,law,g.laws)
 return {m,g,law,shape,matches}
}
test('increment never substitutes the weaker vote law when its guarded factor is absent',()=>counted(fullRate,()=>{
 const {m,g,law,shape,matches}=incrementFixture()
 expect(discoverLiftedCountOperation(m,shape,4)?.kind).toBe('threshold-increment')
 expect(matches.length).toBeGreaterThan(0);expect(shape.countShape.weakerLaw).toBeDefined()
 const offered=g.laws.filter(candidate=>!matches.some(match=>match.law===candidate)),events:Record<string,unknown>[]=[]
 let requests=0
 const proof=proveLiftedCountIncrement(m,offered,law,clock()+2000,()=>{requests++;throw Error('missing guarded premise reached proof search')},event=>events.push(event))
 expect(proof).toBeUndefined();expect(requests).toBe(0)
 expect(events).toContainEqual({stage:'increment-decline',reason:'no-unique-guarded-vote-premise'})
},true))
test('input-self restrictions do not hide the unique source indicator counter',()=>{
 const {m,g,law,shape}=incrementFixture(),before=discoverLiftedCountOperation(m,shape,4)
 expect(before?.kind).toBe('threshold-increment')
 if(!before||!('write'in before)||!before.write)throw Error('missing increment write')
 const prepared=restrictedCounts(m,[before.write.inputCount],8).machine,afterShape=discoverLiftedCountGuard(prepared,law,g.laws)!
 expect(Object.keys(prepared.counts!).length).toBeGreaterThan(Object.keys(m.counts!).length)
 expect(discoverLiftedCountOperation(prepared,afterShape,4)).toEqual(before)
})
