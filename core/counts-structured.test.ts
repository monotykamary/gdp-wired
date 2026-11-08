import {expect,test} from 'bun:test'
import {type Law,type Machine,all,any,get,ite,n,not,plus,same,x} from './machine.ts'
import {admitCountedFamily,countsDump} from './counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../kernel/prove.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'

test('failed ordinary families can use structured witnesses without accepting a false partition',()=>{
 const key=x('member'),whole=same(get('Whole',key),n(1)),inside=same(get('Inside',key),n(1)),base={j:'unused',key:'member',below:n(3)}
 const m:Machine={name:'arbitrary refreshed partition',params:[],inputs:[],inputMaps:['NextWhole','NextInside'],state:{active:n(0)},maps:{Whole:0,Inside:0},counts:{
  All:{...base,body:ite(whole,n(1),n(0))},
  In:{...base,body:ite(all(whole,inside),n(1),n(0))},
  Out:{...base,body:ite(all(whole,not(inside)),n(1),n(0))},
 },step:{state:{active:n(1)},maps:{Whole:{each:'cell',value:get('NextWhole',x('cell'))},Inside:{each:'cell',value:get('NextInside',x('cell'))}}}}
 // Initialization is trivial; refreshed maps force a structured step proof.
 for(const wrong of [false,true]){
  const sum=plus(get('In',n(0)),get('Out',n(0)))
  const law:Law={name:wrong?'off-by-one partition':'partition remains exact',holds:any(same(x('active'),n(0)),same(get('All',n(0)),wrong?plus(sum,n(1)):sum))}
  const old=countsDump.on,phases:string[]=[]
  countsDump.on=e=>{if('phase'in e&&typeof e.phase==='string')phases.push(e.phase)}
  try{
   const result=withWall(performance.now()+6000,()=>counted(fullRate,()=>{
    const until=clock()+3000
    return withDeadline(until,()=>admitCountedFamily(m,[law],[law],new Set(),until))
   },true))
   expect(phases).toContain('structured-family-expansion')
   expect(result.proven).toBe(!wrong)
   if(result.proof){
    expect(Object.values(result.proof.certs).some(c=>c.insts.some(i=>i.terms.length>=3))).toBe(true)
    expect(checkCountedLaws(m,result.laws,result.proof)).toBe(true)
   }
  }finally{countsDump.on=old}
 }
},10000)
