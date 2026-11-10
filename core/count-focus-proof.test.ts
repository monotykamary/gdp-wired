import {expect,test} from 'bun:test'
import {type Law,type Machine,all,any,atMost,get,n,same,x} from './machine.ts'
import {checkCountedLaws,type CountCert} from '../kernel/kernel.ts'
import {clock} from '../kernel/prove.ts'
import {certFor} from './counts.ts'
import {focusedCountRecoveryEnabled,proveFocusedCounts} from './count-focus-proof.ts'

test('finite-input focused recovery is the default and keeps an explicit opt-out',()=>{
 const m:Machine={name:'finite',params:[],inputs:['choice'],state:{},assume:any(...[0,1,2].map(i=>same(x('choice'),n(i)))),step:{}}
 expect(focusedCountRecoveryEnabled(m,'')).toBe(true)
 expect(focusedCountRecoveryEnabled(m,'0')).toBe(false)
 const other:Machine={name:'not finite',params:[],inputs:[],state:{},step:{}}
 expect(focusedCountRecoveryEnabled(other,'')).toBe(false)
 expect(focusedCountRecoveryEnabled(other,'1')).toBe(true)
})
test('focused finite-count recovery keeps the selected step packet instead of rebuilding its full pool',()=>{
 const m:Machine={name:'finite carried count',params:[],inputs:['action'],inputMaps:['Input'],state:{value:n(0)},counts:{Rows:{j:'rowA',key:'memberA',below:n(2),body:n(1)},Limit:{j:'rowB',key:'memberB',below:n(2),body:n(1)}},assume:all(any(...[0,1,2].map(i=>same(x('action'),n(i)))),same(get('Limit',n(0)),n(2))),step:{state:{value:get('Rows',n(0))}}}
 const law:Law={name:'bounded',holds:atMost(x('value'),n(2))},events:Record<string,unknown>[]=[]
 const result=proveFocusedCounts(m,[law],law,{},clock()+5000,(goal,decls)=>{
  const proposed=certFor(goal,decls,true,16),rows=proposed.reads.find(r=>r[1]==='Rows'),limit=proposed.reads.find(r=>r[1]==='Limit')
  if(!rows||!limit)return proposed
  const insts:CountCert['insts']=[{wit:'unused$direction',below:n(2),terms:[[1,limit[0]],[-1,rows[0]]],unit:0},{wit:'needed$direction',below:n(2),terms:[[1,rows[0]],[-1,limit[0]]],unit:0}]
  return {reads:proposed.reads,insts}
 },e=>events.push(e))
 expect(result).toBeDefined()
 if(result){
  const step=Object.entries(result.certs).find(([name])=>name.endsWith('@step'))![1]
  expect(step.insts.map(i=>i.wit)).toEqual(['needed$direction'])
  expect(checkCountedLaws(m,[law],{instances:{[law.name]:result.instances},certs:result.certs})).toBe(true)
 }
 expect(events.some(e=>e.stage==='focused-step-certificate'&&e.after===1)).toBe(true)
})
