import {expect,test} from 'bun:test'
import {type Law,type Machine,n,x,get,same} from '../core/machine.ts'
import {type Goal} from './kernel.ts'
import {effectiveModelRounds,withModelRounds,modelRounds,withModels,withWall,proveSetFast,memoReuseStats} from './prove.ts'
import {env} from '../core/solver.ts'
const m:Machine={name:'six refinement rounds',params:[],inputs:[],state:{},maps:{A:0},step:{}}
const law:Law={name:'zero rows',forall:'k',holds:same(get('A',x('k')),n(0))}
type Answer={stuck:'sat'|'unknown',goal:Goal,witness?:Record<string,number>,why?:string}
const sequence=()=>{
 let queries=0
 const out=withModels<Answer>(m,[law],{},()=>{const row=`row${queries}`;return[{name:'six @step',hyps:[same(get('A',x(row)),n(queries<6?1:0))]}]},gs=>{const i=queries++;return{stuck:'sat',goal:gs[0]!,witness:{[`row${i}`]:i+1,[`A[row${i}:1]`]:i<6?1:0}} as Answer},a=>a.stuck==='sat'?{goal:a.goal,w:a.witness!}:undefined,a=>a.stuck==='sat',(a,why)=>({stuck:'unknown',goal:a.goal,why}))
 return{queries,...out.result}
}
test('default four is unchanged; numeric and progress opt-ins confirm after six refinements',()=>{
 expect(modelRounds).toBe(4)
 expect(withModelRounds(4,sequence)).toMatchObject({queries:5,stuck:'unknown',why:'unconfirmed model: round limit reached'})
 expect(withModelRounds(8,sequence)).toMatchObject({queries:7,stuck:'sat'})
 expect(withModelRounds('progress',sequence)).toMatchObject({queries:7,stuck:'sat'})
})
test('environment, nested override and exceptions restore the effective policy',()=>{
 const old=env.GDP_MODEL_ROUNDS
 try{
  delete env.GDP_MODEL_ROUNDS;expect(effectiveModelRounds()).toBe(4)
  env.GDP_MODEL_ROUNDS='12';expect(effectiveModelRounds()).toBe(12)
  withModelRounds('progress',()=>{expect(effectiveModelRounds()).toBe('progress');expect(()=>withModelRounds(6,()=>{expect(effectiveModelRounds()).toBe(6);throw Error('restore')})).toThrow();expect(effectiveModelRounds()).toBe('progress')})
  expect(effectiveModelRounds()).toBe(12)
  for(const bad of ['','-1','1.5','NaN','Infinity','9007199254740992','01']){env.GDP_MODEL_ROUNDS=bad;expect(()=>effectiveModelRounds()).toThrow()}
 }finally{if(old===undefined)delete env.GDP_MODEL_ROUNDS;else env.GDP_MODEL_ROUNDS=old}
 for(const bad of [-1,NaN,Infinity,1.5])expect(()=>withModelRounds(bad,()=>0)).toThrow()
})
test('progress does not renew an expired caller wall',()=>{
 const out=withModelRounds('progress',()=>withWall({domain:'real',end:-1},sequence))
 expect(out).toMatchObject({queries:1,stuck:'unknown',why:'unconfirmed model: wall reached'})
})
test('positive and negative memos are isolated by effective round policy',()=>{
 for(const bad of [false,true]){
  const machine:Machine={name:`round memo ${bad}`,params:[],inputs:[],state:{value:n(bad?1:0)},maps:{A:0},step:{}}
  const ls:Law[]=[{name:'value zero',holds:same(x('value'),n(0))}]
  const ask=(policy:number|'progress')=>withModelRounds(policy,()=>proveSetFast(machine,ls))
  expect(ask(8).proven).toBe(!bad)
  const hits=bad?memoReuseStats.modelHits:memoReuseStats.setHits
  expect(ask(4).proven).toBe(!bad)
  expect(bad?memoReuseStats.modelHits:memoReuseStats.setHits).toBe(hits)
  expect(ask(4).proven).toBe(!bad)
  expect(bad?memoReuseStats.modelHits:memoReuseStats.setHits).toBeGreaterThan(hits)
 }
})
