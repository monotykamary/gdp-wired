import {expect,spyOn,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {type Law,type Machine,n,same,x} from './machine.ts'
import * as kernel from '../kernel/kernel.ts'
import * as scopes from './count-proof-scope.ts'
import {clock,grow,withDeadline,withWall,BudgetExpired} from '../kernel/prove.ts'
import {type CountLawProof,scopeCountProof,isCheckedReducedScope} from './count-proof-scope.ts'
import {rescopeCountProof,type CountRescopeEvent} from './count-proof-rescope.ts'
import {greatestClosedCountFamily} from './count-closed-family.ts'
const bounded=<T>(run:(until:number)=>T)=>withWall(performance.now()+10000,()=>withDeadline(clock()+10000,()=>run(clock()+9000)))
function fixture(){
 const m:Machine={name:'reduced context control',params:[],inputs:[],state:{a:n(0),b:n(0),noise:n(0)},step:{state:{a:x('b'),b:x('a')}}}
 const a:Law={name:'left',holds:same(x('a'),n(0))},b:Law={name:'right',holds:same(x('b'),n(0))},noise:Law={name:'unrelated',holds:same(x('noise'),n(9))}
 return {m,a,b,noise,family:[noise,a,b]}
}
function prove(f:ReturnType<typeof fixture>,until:number):CountLawProof{
 const certs:Record<string,kernel.CountCert>={};for(const {goal,decls}of kernel.countedObligations(f.m,f.family,{},f.family.indexOf(f.a))){const base={reads:[],insts:[]},expanded=kernel.mcGoal(goal.hyps,decls,base)!,r=grow(expanded,new Map(),{nodes:0,until});if(!('tree'in r))throw Error('fixture did not close');certs[goal.name]={...base,tree:r.tree}}return {instances:{},certs}
}
test('46.10 negative1: omitted premise refuses reduction; funded full fallback stays unchecked',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),premises:[]},events:CountRescopeEvent[]=[],native=spyOn(kernel,'checkMC');let permits=0
 try{const r=rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,e=>events.push(e),{allowFullFallback:()=>{permits++;return true}})!;expect(r).toBeDefined();expect(r.proof.status).toBe('unchecked');expect(isCheckedReducedScope(r,f.m)).toBe(false);expect(r.premises.map(p=>p.name)).toContain(f.b.name);expect(events.map(e=>[e.stage,e.checked])).toEqual([['canonical',false],['original',true]]);expect(native).toHaveBeenCalledTimes(2);expect(permits).toBe(1)}finally{native.mockRestore()}
}))
test('46.10 negative2: unused declared/held laws disappear; one native INIT/STEP pass',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),premises:f.family.map(l=>l.name)},events:CountRescopeEvent[]=[],native=spyOn(kernel,'checkMC');let fallback=0
 try{const r=rescopeCountProof(f.m,f.a,f.family,proof,new Set(f.family.map(l=>l.name)),until,e=>events.push(e),{allowFullFallback:()=>{fallback++;return true}})!;expect(r).toBeDefined();expect(r.premises.map(p=>p.name)).toEqual([f.b.name]);expect(isCheckedReducedScope(r,f.m,f.family)).toBe(true);expect(events.map(e=>[e.stage,e.checked])).toEqual([['canonical',true]]);expect(native).toHaveBeenCalledTimes(2);expect(fallback).toBe(0)}finally{native.mockRestore()}
}))
test('46.10 negative3: unchecked proposals require both checks and reject corrupt STEP',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),status:'unchecked' as const},native=spyOn(kernel,'checkMC')
 try{const good=rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until)!;expect(good.proof.status).toBeUndefined();expect(isCheckedReducedScope(good,f.m)).toBe(true);expect(native).toHaveBeenCalledTimes(2);native.mockClear();const name=f.a.name+' @step',bad={...proof,certs:{...proof.certs,[name]:{...proof.certs[name]!,tree:{leaf:[]}}}};expect(rescopeCountProof(f.m,f.a,f.family,bad,new Set(),until)).toBeUndefined();expect(native).toHaveBeenCalledTimes(1)}finally{native.mockRestore()}
}))
test('46.10 negative4: full-only acceptance cannot suppress recorded/recipe-known requirements',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),premises:[]},r=rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,undefined,{allowFullFallback:()=>true})!,known=['recipe-known-unheld'],effective=isCheckedReducedScope(r,f.m)?r.premises.map(p=>p.name):[...new Set([...r.premises.map(p=>p.name),...known])];expect(effective).toContain(f.b.name);expect(effective).toContain(known[0]!);const plan=greatestClosedCountFamily([f.a.name],new Map([[f.a.name,effective]]));expect(plan.members).toEqual([]);expect(plan.blockers).toContain(known[0]!)
}))
test('opaque receipts bind certificate, machine, owner, context and sources',()=>bounded(until=>{
 const f=fixture(),r=rescopeCountProof(f.m,f.a,f.family,prove(f,until),new Set(),until)!
 expect(isCheckedReducedScope(r,f.m)).toBe(true);expect(isCheckedReducedScope({...r,checkedReduced:{kind:'checked-reduced'}},f.m)).toBe(false);expect(isCheckedReducedScope({...r,checkedReduced:structuredClone(r.checkedReduced)},f.m)).toBe(false);expect(isCheckedReducedScope({...r,proof:{...r.proof,status:'unchecked'}},f.m)).toBe(false);expect(isCheckedReducedScope({...r,proof:{...r.proof,certs:{}}},f.m)).toBe(false);expect(isCheckedReducedScope({...r,owner:{...r.owner,name:'other'}},f.m)).toBe(false);expect(isCheckedReducedScope({...r,premises:[]},f.m)).toBe(false);expect(isCheckedReducedScope({...r,sources:[]},f.m)).toBe(false);expect(isCheckedReducedScope(r,{...f.m,state:{...f.m.state,a:n(1)}})).toBe(false);expect(isCheckedReducedScope(r,f.m,[f.a,{...f.b,holds:same(x('b'),n(1))}])).toBe(false);f.b.holds=same(x('b'),n(1));expect(isCheckedReducedScope(r,f.m)).toBe(false)
}))
test('FULL controller context uses the metered structural encoder, not scalar workJSON',()=>bounded(()=>{
 const f=fixture(),first=scopes.countScopeContextKey(f.m,f.family)
 expect(first).toBe(scopes.countScopeContextKey(structuredClone(f.m),structuredClone(f.family)))
 expect(first).not.toBe(scopes.countScopeContextKey({...f.m,state:{...f.m.state,a:n(1)}},f.family))
}))
test('scope capture and forged flags are not native receipts',()=>bounded(until=>{const f=fixture(),r=scopeCountProof(f.m,f.a,f.family,prove(f,until),until)!;expect(isCheckedReducedScope(r,f.m)).toBe(false);expect(isCheckedReducedScope({...r,checkedReduced:{kind:'checked-reduced'}},f.m)).toBe(false)}))
test('default/explicit denial starts no fallback; hard errors propagate',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),premises:[]},native=spyOn(kernel,'checkMC');let permits=0
 try{expect(rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until)).toBeUndefined();expect(rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,undefined,{allowFullFallback:()=>{permits++;return false}})).toBeUndefined();expect(permits).toBe(1);expect(native).not.toHaveBeenCalled();const stop=new BudgetExpired('cancelled fallback');expect(()=>rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,()=>{throw stop},{allowFullFallback:()=>{permits++;return true}})).toThrow(stop);expect(permits).toBe(1);expect(native).not.toHaveBeenCalled()}finally{native.mockRestore()}
}))
test('false full fallback is refused, not converted to unchecked success',()=>bounded(until=>{const f=fixture(),proof={...prove(f,until),premises:[]},name=f.a.name+' @step';proof.certs[name]={...proof.certs[name]!,tree:{leaf:[]}};const events:CountRescopeEvent[]=[];expect(rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,e=>events.push(e),{allowFullFallback:()=>true})).toBeUndefined();expect(events.map(e=>[e.stage,e.checked])).toEqual([['canonical',false],['original',false]])}))
test('native false INIT, false STEP and changed context are never accepted',()=>bounded(until=>{
 const f=fixture(),proof=prove(f,until)
 for(const [m,family]of [[{...f.m,state:{...f.m.state,a:n(1)}},f.family],[{...f.m,step:{state:{...f.m.step.state,a:n(1)}}},f.family],[f.m,[f.noise,f.a,{...f.b,holds:same(x('b'),n(1))}]]] as const){const events:CountRescopeEvent[]=[];expect(rescopeCountProof(m,f.a,[...family],proof,new Set(),until,e=>events.push(e),{allowFullFallback:()=>true})).toBeUndefined();expect(events.some(e=>e.checked)).toBe(false)}
}))
test('denied funded replay can retain only the captured unchecked offer without recapture',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),premises:f.family.map(law=>law.name)},replay=spyOn(scopes,'replayScopedCountProof'),capture=spyOn(scopes,'scopeCountProofPair'),native=spyOn(kernel,'checkMC')
 let offered:scopes.ScopedCountProof|undefined
 replay.mockImplementationOnce(()=>undefined)
 try{
  const result=rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,undefined,{retainUncheckedOffer:true,allowFullFallback:value=>{offered=value;return false}})!
  expect(result).toBeDefined();expect(result.proof.status).toBe('unchecked');expect(result.checkedReduced).toBeUndefined()
  expect(result.premises).toBe(offered!.premises);expect(result.sources).toBe(offered!.sources);expect(result.proof.certs).toBe(offered!.proof.certs)
  expect(capture).toHaveBeenCalledTimes(1);expect(native).not.toHaveBeenCalled()
 }finally{replay.mockRestore();capture.mockRestore();native.mockRestore()}
}))
test('funded full-only success reuses offered scope without another capture or reduced stamp',()=>bounded(until=>{
 const f=fixture(),proof={...prove(f,until),premises:f.family.map(law=>law.name)},replay=spyOn(scopes,'replayScopedCountProof'),capture=spyOn(scopes,'scopeCountProofPair')
 let offered:scopes.ScopedCountProof|undefined
 replay.mockImplementationOnce(()=>undefined)
 try{
  const result=rescopeCountProof(f.m,f.a,f.family,proof,new Set(),until,undefined,{allowFullFallback:value=>{offered=value;return true}})!
  expect(result.proof.status).toBe('unchecked');expect(result.checkedReduced).toBeUndefined()
  expect(result.premises).toBe(offered!.premises);expect(result.sources).toBe(offered!.sources);expect(capture).toHaveBeenCalledTimes(1)
 }finally{replay.mockRestore();capture.mockRestore()}
}))

test('zero complete-work lease publishes no scope and starts no fallback',()=>bounded(until=>{
 const f=fixture(),proof=prove(f,until),env=Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),child=spawnSync(process.execPath,['--eval',`import {strict as a} from 'node:assert';import {rescopeCountProof} from './core/count-proof-rescope.ts';import {withBudget,fullWork,BudgetExpired} from './kernel/prove.ts';const {m,owner:givenOwner,family,proof}=JSON.parse(process.env.S46_INPUT);const owner=family.find(l=>l.name===givenOwner.name);const before=fullWork();let permits=0,stopped=false,result;try{result=withBudget(0,()=>rescopeCountProof(m,owner,family,proof,new Set(),Infinity,undefined,{allowFullFallback:()=>{permits++;return true}}))}catch(e){a(e instanceof BudgetExpired);stopped=true}a(stopped);a.equal(result,undefined);a.equal(fullWork(),before);a.equal(permits,0)`],{cwd:new URL('../',import.meta.url).pathname,env:{...env,GDP_WORK_FULL:'1',S46_INPUT:JSON.stringify({m:f.m,owner:f.a,family:f.family,proof})},encoding:'utf8',timeout:10000});if(child.status!==0)throw Error(child.stderr);expect(child.status).toBe(0)
}))
