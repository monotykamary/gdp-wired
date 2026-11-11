import {expect,test} from 'bun:test'
import {type Law,type Machine,n,same} from './machine.ts'
import {clock} from '../kernel/prove.ts'
import {proveLiftedCountLoad} from './count-lifted-load.ts'
import {proveLiftedCountCopy} from './count-lifted-copy.ts'
import {proveLiftedCountIncrement} from './count-lifted-increment.ts'
import {proveLiftedCountReplacement} from './count-lifted-replacement.ts'
import {proveLiftedCountComposition} from './count-lifted-strategy.ts'
for(const [name,emit]of [['load',proveLiftedCountLoad],['copy',proveLiftedCountCopy],['increment',proveLiftedCountIncrement],['replacement',proveLiftedCountReplacement],['composition',proveLiftedCountComposition]]as const){
 test(name+' rejects an unoffered target before inspecting the machine or requesting a proof',()=>{
  const machine=new Proxy({}as Machine,{get(){throw Error('unoffered target inspected the machine')}}),law:Law={name:'unoffered',holds:same(n(0),n(0))}
  const result=emit(machine,[],law,clock()+500,()=>{throw Error('unoffered target requested a proof')})
  expect(result).toBeUndefined()
 })
}
