import {expect,test} from 'bun:test'
import {type Law,type Machine,n,x} from './machine.ts'
import {countedAttempts,countsDump} from './counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../kernel/prove.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'

test('bounded relevance preflight lifts a proof and never promotes a subset model',()=>{
 const target:Law={name:'bounded cells',forall:'k',holds:{op:'<=',a:{op:'get',map:'cells',key:x('k')},b:n(1)}}
 const noise:Law[]=Array.from({length:32},(_,i)=>({name:'frame '+i,holds:{op:'<=',a:n(0),b:{op:'get',map:'spare',key:n(i)}}})),laws=[target,...noise]
 const old=countsDump.on,events:string[]=[];countsDump.on=e=>{if('phase'in e&&typeof e.phase==='string')events.push(e.phase)}
 try{
  for(const value of [1,2]){
   const m:Machine={name:'preflight control',params:[],inputs:['at'],state:{},maps:{cells:0,spare:0},counts:{unused:{j:'member',key:'bucket',below:n(2),body:{op:'get',map:'spare',key:x('member')}}},step:{maps:{cells:{key:x('at'),value:n(value)}}}}
   const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1500;return withDeadline(until,()=>countedAttempts(m,[],new Set([target]),until).traced(target,laws,0,1500))},true))
   expect('proof'in result).toBe(value===1)
   if('proof'in result)for(const {goal,decls}of countedObligations(m,laws,{[target.name]:result.proof.instances},0))expect(checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)).toBe(true)
  }
  expect(events).toContain('preflight-proven')
 }finally{countsDump.on=old}
},10000)
