import {expect,test} from 'bun:test'
import {get,n,x,type Law,type Machine} from '../../core/machine.ts'
import {countedObligations} from '../../kernel/kernel.ts'
import {Meter} from './match.ts'
import {recoverFlags} from './recover-flags.ts'
const m:Machine={name:'flag recovery',params:[],inputs:[],state:{},maps:{R:0},step:{flags:{rows:{op:'all',key:'i',c:{op:'<=',a:get('R',x('i')),b:n(1)}}}}}
const law:Law={name:'bounded',forall:'k',holds:{op:'<=',a:get('R',x('k')),b:n(1)}}
test('flag recovery uses actual machine-generated rows and removes all placeholder names',()=>{
  const original=countedObligations(m,[law],{bounded:{'?rows':[n(2),n(3)]}},0).find(x=>x.goal.name.endsWith('@step'))!
  const out=recoverFlags(original.goal,m,[law],law.name,{},new Meter(100000))
  expect(out.instances).toEqual({'?rows':[n(2),n(3)]});expect(out.base.goal).toEqual(original.goal)
  expect(JSON.stringify(out.instances)).not.toContain('__astra_flag_hole_')
})
test('an absent original flag instance is not invented; template traversal is metered',()=>{
  const original=countedObligations(m,[law],{},0).find(x=>x.goal.name.endsWith('@step'))!
  expect(recoverFlags(original.goal,m,[law],law.name,{},new Meter(100000)).records).toEqual([])
  expect(()=>recoverFlags(original.goal,m,[law],law.name,{},new Meter(1))).toThrow('budget')
})
