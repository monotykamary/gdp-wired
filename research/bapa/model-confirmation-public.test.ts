// Isolated retained solver-result replay through the real public admission path.
import {expect,test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {Cond,Term,nat,proveRule,rule,type MapWrite} from '../../core/dsl.ts'
import {evalC,evalE,type E,type Law,type Machine,type State} from '../../core/machine.ts'
import {obligations} from '../../kernel/kernel.ts'
import {eprScope,keyValue,lawInstances,modelInstances,queryHook,type ModelConfirmation} from '../../kernel/prove.ts'
import {patternsOf} from '../../kernel/epr.ts'
const fixture=JSON.parse(readFileSync(new URL('./fixtures/retained7-model.json',import.meta.url),'utf8')) as {machine:Machine,family:Law[],index:number,witness:Record<string,number>}
const {machine:m,family,index,witness:w}=fixture,target=family[index]!
const env=new Proxy(w,{get:(t,p:string)=>t[p]??0})
const st:State={scalars:{},maps:Object.fromEntries(Object.keys(m.maps??{}).map(k=>[k,new Map<number,number>()]))}
for(const [cell,value]of Object.entries(w)){const mp=cell.slice(0,cell.indexOf('['));if(!st.maps[mp])continue;const k=keyValue(cell,w);if(k!==undefined)st.maps[mp]!.set(k,value)}
const rawRule=()=>rule(m.name).params(Object.fromEntries(m.params.map(k=>[k,nat])))
 .inputs(Object.fromEntries(m.inputs.map(k=>[k,nat])))
 .state(Object.fromEntries(Object.entries(m.state).map(([k,e])=>[k,()=>new Term(e)])))
 .maps(Object.fromEntries(Object.entries(m.maps??{}).filter(([name])=>!(name in (m.relations??{}))))).sorts(...new Set(Object.values(m.relations??{}).flat())).relations(m.relations??{})
 .assume(()=>new Cond(m.assume??{op:'and',xs:[]}))
 .flags(()=>Object.fromEntries(Object.entries(m.step.flags??{}).map(([k,c])=>[k,new Cond(c)])))
 .step(()=>({...Object.fromEntries(Object.entries(m.step.state??{}).map(([k,e])=>[k,new Term(e)])),...Object.fromEntries(Object.entries(m.step.maps??{}).map(([k,v])=>[k,{...v,map:k} as MapWrite]))}) as never)

test('p4 retained CTI violates present seeds 3/8 and both refinements are found',()=>{
 const old=eprScope.patterns;eprScope.patterns=patternsOf(m,family)
 try{
  const inst=lawInstances(m,family,index),goal=obligations(m,family,{[target.name]:inst},index).find(g=>g.name.endsWith(' @step'))!
  const status:ModelConfirmation={confirmed:false},more=modelInstances(m,family,inst,goal,w,64,true,status)
  expect(status.confirmed).toBe(false);expect(more).toBeDefined()
  for(const id of [3,8]){
   const l=family.find(l=>l.name.startsWith(`retained:${id}:`))!,names=[l.forall!,...l.keys??[]]
   expect(evalC(l.holds,{...w,...Object.fromEntries(names.map((n,i)=>[n,[241,764,1571,1][i]!]))},st,m)).toBe(false)
   const all=more?.[l.name]??[],newTerms=all.slice(inst[l.name]?.length??0),tuples:E[][]=[]
   for(let j=0;j<newTerms.length;j+=names.length)tuples.push(newTerms.slice(j,j+names.length))
   expect(tuples.map(es=>es.map(e=>evalE(e,env,st,m)))).toContainEqual([241,764,1571,1])
  }
 }finally{eprScope.patterns=old}
})

test('public proveRule keeps retained:7 when its replayed CTI refinement is unsettled',()=>{
 const r=rawRule(),source=r.machine
 expect(source.step).toEqual(m.step);expect(source.assume).toEqual(m.assume)
 const publicLaws=family.slice(0,2),candidates=[target,...family.slice(2).filter(l=>l!==target)],ordered=[...publicLaws,...candidates]
 const inst=lawInstances(source,ordered,2),full=obligations(source,ordered,{[target.name]:inst},2).find(g=>g.name.endsWith(' @step'))!
 const seen:number[]=[],audits:any[]=[],stop=new Error('stop after real public candidate audit'),old=queryHook.on
 queryHook.on=q=>{
  old?.(q)
  if(!q.goal.name.endsWith(' @step'))return
  const isTarget=q.goal.name===`${target.name} @step`
  if(isTarget)seen.push(q.goal.hyps.length)
  for(const k of Object.keys(q.out))delete (q.out as unknown as Record<string,unknown>)[k]
  Object.assign(q.out,isTarget&&q.goal.hyps.length<=full.hyps.length?{stuck:'sat',witness:{...w}}:{stuck:'unknown',why:'forced unsettled refined query'})
 }
 try{
  expect(()=>proveRule(r as never,publicLaws,{search:true,candidateSeeds:{laws:candidates,report:a=>{audits.push(a);throw stop}}})).toThrow(stop)
  expect(seen.length).toBeGreaterThan(0)
  expect(audits).toHaveLength(1)
  expect(audits[0]).toMatchObject({status:'inconclusive',dropped:[]})
  expect(audits[0].kept).toContain(target.name)
  expect(audits[0].reason).toContain('unknown')
  expect(audits[0].reason).toContain('unconfirmed model')
  expect(r.machine).toEqual(source)
 }finally{queryHook.on=old}
},120000)
