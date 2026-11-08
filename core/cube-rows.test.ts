import {expect, test} from 'bun:test'
import {inferLaws} from './infer.ts'
import {type Machine, type Law, interpret, n, x, get, same} from './machine.ts'
const m: Machine = {name:'shared reachable rows',params:['size'],inputs:['at'],state:{},maps:{A:0,B:0},
 assume:{op:'<',a:x('at'),b:x('size')},step:{maps:{A:{key:x('at'),value:n(1)},B:{key:x('at'),value:get('A',x('at'))}}}}
const law:Law={name:'template',forall:'a',keys:['b'],holds:same(get('A',x('a')),get('B',x('b')))}
const run=interpret(m),params={size:2},start=run.init(params),rows=[{params,st:start},{params,st:run.step(params,start,{at:0})}]
function cubes(input: typeof rows | undefined){
 const events:{phase:string,info:Record<string,number|string>}[]=[]
 const result=inferLaws(m,[law],[],{cubes:2,rows:input,ms:1500,progress:(phase,info)=>events.push({phase,info})})
 return {result,events,runs:events.find(e=>e.phase==='runs')!.info}
}
test('cube-only inference reuses supplied states without another random walk',()=>{
 const before=JSON.stringify(rows.map(r=>[r.params,[...r.st.maps.A!],[...r.st.maps.B!]])),shared=cubes(rows)
 expect(shared.runs.trials).toBe(0);expect(shared.runs.samples).toBe(rows.length)
 expect(shared.result.proven).toBe(false);expect(shared.result.found.length).toBeGreaterThan(0)
 expect(JSON.stringify(rows.map(r=>[r.params,[...r.st.maps.A!],[...r.st.maps.B!]]))).toBe(before)
},10000)
test('absent and empty supplied rows retain random exploration and every cube family',()=>{
 const ordinary=cubes(undefined),empty=cubes([]),shared=cubes(rows)
 expect(ordinary.runs.trials).toBeGreaterThan(0);expect(empty.runs.trials).toBeGreaterThan(0)
 expect(empty.result.found).toEqual(ordinary.result.found)
 expect(shared.result.found).toEqual(ordinary.result.found)
},20000)
