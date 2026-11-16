import {expect,test} from 'bun:test'
import {type Machine,type Law,type E,get,n,x,same} from '../core/machine.ts'
import {type Goal} from './kernel.ts'
import {modelInstances,withModels,withWall,type ModelConfirmation} from './prove.ts'
const m:Machine={name:'confirmation',params:[],inputs:[],state:{},maps:{A:0},step:{}}
const law:Law={name:'zero cells',forall:'key',holds:same(get('A',x('key')),n(0))}
type Answer={stuck:'sat'|'unknown',witness?:Record<string,number>,goal:Goal,why?:string}
const goal=(key='row'):Goal=>({name:'confirmation @step',hyps:[same(get('A',x(key)),n(1))]})
const sat=(g=goal()):Answer=>({stuck:'sat',goal:g,witness:{row:3,'A[row:1]':1}})
const unknown=(a:Answer,why:string):Answer=>({stuck:'unknown',goal:a.goal,why})
const model=(a:Answer)=>a.stuck==='sat'&&a.witness?{goal:a.goal,w:a.witness}:undefined
const settled=(a:Answer)=>a.stuck==='sat'

test('an unsettled refinement never returns its first SAT',()=>{
 let calls=0,refined=false
 const out=withModels(m,[law],{},i=>{if(calls)refined=!!i[law.name]?.length;return[goal()]},gs=>++calls===1?sat(gs[0]):unknown(sat(gs[0]),'forced incomplete solve'),model,settled,unknown)
 expect(calls).toBe(2);expect(refined).toBe(true)
 expect(out.result).toMatchObject({stuck:'unknown',why:'unconfirmed model: refinement unsettled'})
 expect(out.result.witness).toBeUndefined()
})
test('a wall-cut model is unknown, without a stale witness',()=>{
 const out=withWall({domain:'real',end:-1},()=>withModels(m,[law],{},()=>[goal()],()=>sat(),model,settled,unknown))
 expect(out.result).toMatchObject({stuck:'unknown',why:'unconfirmed model: wall reached'})
 expect(out.result.witness).toBeUndefined()
})
test('an already assumed false instance is not a no-more confirmation',()=>{
 const c:ModelConfirmation={confirmed:false}
 expect(modelInstances(m,[law],{[law.name]:[x('row')]},goal(),sat().witness!,64,false,c)).toBeUndefined()
 expect(c).toMatchObject({confirmed:false,why:'model violates a hypothesis instance'})
 const out=withModels(m,[law],{[law.name]:[x('row')]},()=>[goal()],()=>sat(),model,settled,unknown)
 expect(out.result.stuck).toBe('unknown');expect(out.result.witness).toBeUndefined()
})
test('a zero tuple allowance is not confirmation',()=>{
 const c:ModelConfirmation={confirmed:false}
 expect(modelInstances(m,[law],{},goal(),sat().witness!,0,false,c)).toBeUndefined()
 expect(c.confirmed).toBe(false);expect(c.why).toContain('budget')
})
test('the model-round cap never authorizes its current SAT',()=>{
 let round=0
 const out=withModels(m,[law],{},()=>[goal(`row${round}`)],(gs):Answer=>{const r=round++;return{stuck:'sat',goal:gs[0]!,witness:{[`row${r}`]:r+1,[`A[row${r}:1]`]:1}}},model,settled,unknown)
 expect(round).toBe(5);expect(out.result).toMatchObject({stuck:'unknown',why:'unconfirmed model: round limit reached'})
 expect(out.result.witness).toBeUndefined()
})
test('a genuinely confirmed model retains SAT',()=>{
 const valid:Law={...law,holds:{op:'<=',a:get('A',x('key')),b:n(1)}}
 const out=withModels(m,[valid],{},()=>[goal()],()=>sat(),model,settled,unknown)
 expect(out.result).toMatchObject({stuck:'sat',witness:sat().witness})
})
