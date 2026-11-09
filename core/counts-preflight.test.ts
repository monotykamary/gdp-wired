import {expect,test} from 'bun:test'
import {type Law,type Machine,n,x} from './machine.ts'
import {countedAttempts,countsDump} from './counts.ts'
import {clock,counted,fullRate,withinDeadline,withDeadline,withWall} from '../kernel/prove.ts'
import {checkMC,countedObligations} from '../kernel/kernel.ts'

test('bounded relevance preflight lifts a proof and never promotes a subset model',()=>{
 const target:Law={name:'bounded cells',forall:'k',holds:{op:'<=',a:{op:'get',map:'cells',key:x('k')},b:n(1)}}
 const noise:Law[]=Array.from({length:80},(_,i)=>({name:'frame '+i,holds:{op:'<=',a:n(0),b:{op:'get',map:'spare',key:n(i)}}}))
 const old=countsDump.on,events:{phase:string,hyps:number}[]=[];countsDump.on=e=>{if('phase'in e&&typeof e.phase==='string')events.push({phase:e.phase,hyps:'hyps'in e&&Array.isArray(e.hyps)?e.hyps.length:0})}
 try{
  for(const size of [0,32,80])for(const value of [1,2]){
   const laws=[target,...noise.slice(0,size)]
   const m:Machine={name:'preflight control',params:[],inputs:['at'],state:{},maps:{cells:0,spare:0},counts:{unused:{j:'member',key:'bucket',below:n(2),body:{op:'get',map:'spare',key:x('member')}}},step:{maps:{cells:{key:x('at'),value:n(value)}}}}
   const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{const until=clock()+1500;return withDeadline(until,()=>countedAttempts(m,[],new Set([target]),until).traced(target,laws,0,1500))},true))
   expect('proof'in result).toBe(value===1)
   if('proof'in result)for(const {goal,decls}of countedObligations(m,laws,{[target.name]:result.proof.instances},0))expect(checkMC(goal.hyps,decls,result.proof.certs[goal.name]!)).toBe(true)
  }
  expect(events.some(e=>e.phase==='preflight-proven'&&e.hyps<=64)).toBe(true)
  expect(events.some(e=>e.phase==='preflight-proven'&&e.hyps>64)).toBe(true)
 }finally{countsDump.on=old}
},10000)

test('counted model queries inherit the attempt end, not the outer allowance', () => {
 const m:Machine={name:'attempt cap',params:[],inputs:[],state:{},maps:{A:0},counts:{Total:{j:'row',key:'key',below:n(2),body:{op:'get',map:'A',key:x('key')}}},step:{maps:{A:{key:n(0),value:n(1)}}}}
 const law:Law={name:'empty count',holds:{op:'=',a:{op:'get',map:'Total',key:n(0)},b:n(0)}}
 const prior=countsDump.on
 try {
  for(const pass of [0,1] as const) counted(fullRate,()=>{
   const end=clock()+100, observed:number[]=[]
   countsDump.on=e=>{if('phase'in e&&e.phase==='query')observed.push(withinDeadline(Infinity))}
   withDeadline(end+5000,()=>countedAttempts(m,[law],new Set(),end+5000).traced(law,[law],pass,100))
   expect(observed.length).toBeGreaterThan(0)
   expect(observed.every(x=>x<=end)).toBe(true)
  },true)
 }finally{countsDump.on=prior}
})
