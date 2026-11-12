import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {type Law,type Machine,get,n,same,x} from './machine.ts'
import {type CountCert,type Instances,canon,checkCountedLaws,checkMC,countedObligations,leafConstraintsReusing,lemmaPath,mcGoal} from '../kernel/kernel.ts'
import {refuteFast} from './solver.ts'
import {clock,grow,withDeadline,withWall} from '../kernel/prove.ts'
import {type CountLawProof,scopeCountProof,replayScopedCountProof} from './count-proof-scope.ts'
import {admitCountedFamily,countsDump} from './counts.ts'
import {cdclStats} from '../kernel/cdcl.ts'
import {rescopeCountProof} from './count-proof-rescope.ts'
import {completeWorkProfile} from './work-profile.ts'
import {stepWorkProfile} from './step-work.ts'
import {BudgetExpired} from './work-admission.ts'
import {WallExpired} from './wall.ts'

function fixture(){
 const m:Machine={name:'mutual cell preservation',params:[],inputs:[],state:{left:n(0),right:n(0),noise:n(0)},maps:{extra:0},step:{state:{left:x('right'),right:x('left')}}}
 const left:Law={name:'left remains zero',holds:same(x('left'),n(0))},right:Law={name:'right remains zero',holds:same(x('right'),n(0))}
 const scalar:Law={name:'unused scalar',holds:same(x('noise'),n(7))},indexed:Law={name:'unused indexed',forall:'k',holds:same(get('extra',x('k')),n(2))}
 return {m,left,right,scalar,indexed,family:[scalar,indexed,left,right]}
}
// A past requested deadline is a hard scope-entry/cancellation in counted
// profiles. It must not be converted to a semantic proof refusal.
const expectExpired=(run:()=>unknown):void=>{
 if(completeWorkProfile.enabled)expect(run).toThrow(BudgetExpired)
 else if(stepWorkProfile.enabled)expect(run).toThrow(WallExpired)
 else expect(run()).toBeUndefined()
}
const bounded=<T>(run:(until:number)=>T):T=>withWall(performance.now()+5000,()=>{const until=clock()+2000;return withDeadline(until,()=>run(until))})
const withScopes=<T>(run:(until:number)=>T,enabled='1'):T=>{
 const previous=process.env.GDP_COUNT_STRATEGIES
 process.env.GDP_COUNT_STRATEGIES=enabled
 try{return bounded(run)}finally{if(previous===undefined)delete process.env.GDP_COUNT_STRATEGIES;else process.env.GDP_COUNT_STRATEGIES=previous}
}
function prove(m:Machine,owner:Law,family:Law[],until:number,instances:Instances={}):CountLawProof{
 const certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:instances},family.indexOf(owner))){
  const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)!
  const result=grow(expanded,new Map(),{nodes:0,until})
  if(!('tree'in result))throw Error('fixture proof did not close: '+goal.name)
  certs[goal.name]={...base,tree:result.tree}
 }
 return {instances,certs}
}

test('checked re-scope removes declared but unused premises without searching',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.left,f.family,until,{[f.indexed.name]:[n(0)]})
 const offered={...proof,status:'unchecked' as const,premises:f.family.map(l=>l.name)}
 const before=cdclStats.runs,scoped=rescopeCountProof(f.m,f.left,f.family,offered,new Set(),until)!
 expect(scoped).toBeDefined();expect(scoped.proof.status).toBeUndefined()
 expect(scoped.premises.map(p=>p.name)).toEqual([f.right.name])
 expect(scoped.checkWork).toBeGreaterThanOrEqual(0)
 expect(scoped.proof.instances[f.indexed.name]).toBeUndefined()
 expect(cdclStats.runs).toBe(before)
 expect(replayScopedCountProof(f.m,[f.left,f.right],scoped,until)).toBeDefined()
 expect(replayScopedCountProof(f.m,[f.left],scoped,until)).toBeUndefined()
}))
test('checked re-scope refuses a damaged unchecked packet and expired scope',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.left,f.family,until)
 const bad={...proof,status:'unchecked' as const,certs:{...proof.certs,[f.left.name+' @step']:{...proof.certs[f.left.name+' @step']!,tree:{leaf:[]}}}}
 expect(rescopeCountProof(f.m,f.left,f.family,bad,new Set(),until)).toBeUndefined()
 expectExpired(()=>rescopeCountProof(f.m,f.left,f.family,proof,new Set(),clock()-1))
 expect(rescopeCountProof({...f.m,step:{state:{left:n(1),right:x('left')}}},f.left,f.family,proof,new Set(),until)).toBeUndefined()
}))

test('record referenced laws, not every available scalar or instantiated law',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.left,f.family,until,{[f.indexed.name]:[n(0)]})
 const scoped=scopeCountProof(f.m,f.left,f.family,proof,until)!
 expect(scoped).toBeDefined()
 expect(scoped.premises.map(p=>p.name)).toEqual([f.right.name])
 expect(scoped.proof.premises).toEqual([f.right.name])
 const retained=replayScopedCountProof(f.m,[f.left,f.right],scoped,until)!
 expect(retained).toBeDefined();expect(retained.instances[f.indexed.name]).toBeUndefined()
 const other=prove(f.m,f.right,[f.left,f.right],until)
 expect(checkCountedLaws(f.m,[f.left,f.right],{instances:{[f.left.name]:retained.instances,[f.right.name]:other.instances},certs:{...retained.certs,...other.certs}})).toBe(true)
}))

test('premise matching ignores AST property insertion order',()=>bounded(until=>{
 const f=fixture();f.right.holds={b:n(0),a:x('right'),op:'='}
 const proof=prove(f.m,f.left,f.family,until),scoped=scopeCountProof(f.m,f.left,f.family,proof,until)!
 expect(scoped.premises.map(p=>p.name)).toEqual([f.right.name])
 expect(replayScopedCountProof(f.m,[f.left,f.right],scoped,until)).toBeDefined()
 expect(replayScopedCountProof(f.m,[f.left],scoped,until)).toBeUndefined()
}))

test('independent cut source slices remain premises even if the main tree does not cite the cut',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.left,f.family,until)
 const {goal,decls}=countedObligations(f.m,f.family,{[f.left.name]:proof.instances},f.family.indexOf(f.left))[1]!
 const cert=proof.certs[goal.name]!,expanded=mcGoal(goal.hyps,decls,cert)!
 const index=goal.hyps.findIndex(h=>JSON.stringify(h)===JSON.stringify(f.scalar.holds))
 expect(index).toBeGreaterThanOrEqual(0)
 const cut={noise:1,'1':-7},path=new Map([[canon(cut),{lin:cut,holds:false}]])
 const source={name:'independent cut',hyps:[goal.hyps[index]!]}
 const leaf=refuteFast(leafConstraintsReusing(source,path),256)
 if(leaf?.kind!=='refuted')throw Error('independent cut fixture did not close')
 const lemma={when:[],cut,slice:[index],tree:{leaf:leaf.steps}},lemmas=[lemma]
 const result=grow(expanded,lemmaPath(lemmas,new Map()),{nodes:0,until})
 if(!('tree'in result))throw Error('cut-bearing main tree did not close')
 proof.certs[goal.name]={...cert,lemmas,tree:result.tree}
 expect(checkMC(goal.hyps,decls,proof.certs[goal.name]!)).toBe(true)
 const scoped=scopeCountProof(f.m,f.left,f.family,proof,until)!
 expect(scoped.premises.map(p=>p.name)).toContain(f.scalar.name)
 expect(replayScopedCountProof(f.m,[f.left,f.right],scoped,until)).toBeUndefined()
}))

test('reordering and adding unused laws reindexes but never searches',()=>bounded(until=>{
 const f=fixture(),scoped=scopeCountProof(f.m,f.left,f.family,prove(f.m,f.left,f.family,until),until)!
 const old=cdclStats.on;cdclStats.on=true
 try{
  const before=cdclStats.runs
  const extra:Law={name:'tautology',holds:same(n(0),n(0))}
  expect(replayScopedCountProof(f.m,[extra,f.right,f.left],scoped,until)).toBeDefined()
  expect(cdclStats.runs).toBe(before)
 }finally{cdclStats.on=old}
}))

test('removing an actual premise or changing its body invalidates retention',()=>bounded(until=>{
 const f=fixture(),scoped=scopeCountProof(f.m,f.left,f.family,prove(f.m,f.left,f.family,until),until)!
 expect(replayScopedCountProof(f.m,[f.left],scoped,until)).toBeUndefined()
 expect(replayScopedCountProof(f.m,[f.left,{...f.right,holds:same(x('right'),n(1))}],scoped,until)).toBeUndefined()
 expect(replayScopedCountProof(f.m,[{...f.left,holds:same(x('left'),n(1))},f.right],scoped,until)).toBeUndefined()
 expect(replayScopedCountProof(f.m,structuredClone([f.left,f.right]),scoped,until)).toBeDefined()
}))

test('declared strategy scopes cannot omit used premises or invent names',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.left,f.family,until)
 expect(scopeCountProof(f.m,f.left,f.family,{...proof,premises:[]},until)).toBeUndefined()
 expect(scopeCountProof(f.m,f.left,f.family,{...proof,premises:[f.right.name,'absent']},until)).toBeUndefined()
 expect(scopeCountProof(f.m,f.left,f.family,{...proof,premises:[f.right.name,f.right.name]},until)).toBeUndefined()
 expect(scopeCountProof(f.m,f.left,f.family,{...proof,premises:[f.right.name]},until)).toBeDefined()
}))

test('mutated original laws do not mutate recorded premise identities',()=>bounded(until=>{
 const f=fixture(),scoped=scopeCountProof(f.m,f.left,f.family,prove(f.m,f.left,f.family,until),until)!
 f.right.holds=same(x('right'),n(1))
 expect(replayScopedCountProof(f.m,f.family,scoped,until)).toBeUndefined()
}))

test('changed machine or damaged certificate still requires the current kernel check',()=>bounded(until=>{
 const f=fixture(),scoped=scopeCountProof(f.m,f.left,f.family,prove(f.m,f.left,f.family,until),until)!
 const changed={...f.m,step:{state:{left:n(1),right:x('left')}}}
 expect(replayScopedCountProof(changed,[f.left,f.right],scoped,until)).toBeUndefined()
 const key=f.left.name+' @step',bad={...scoped,proof:{...scoped.proof,certs:{...scoped.proof.certs,[key]:{...scoped.proof.certs[key]!,tree:{leaf:[]}}}}}
 expect(replayScopedCountProof(f.m,[f.left,f.right],bad,until)).toBeUndefined()
 expectExpired(()=>replayScopedCountProof(f.m,[f.left,f.right],scoped,clock()-1))
 expect(scopeCountProof(f.m,f.left,f.family,scoped.proof,clock()-1)).toBeUndefined()
}))

test('a mutual induction cycle survives unrelated drops with checks only in round one',()=>withScopes(until=>{
 const f=fixture(),prior=countsDump.on,events:Record<string,unknown>[]=[]
 countsDump.on=e=>events.push(e as Record<string,unknown>)
 try{
  const result=admitCountedFamily(f.m,[f.left],f.family,new Set(),until)
  expect(result.proven).toBe(true);expect(result.laws).toEqual([f.left,f.right])
  expect(result.proof).toBeDefined();expect(checkCountedLaws(result.m,result.laws,result.proof!)).toBe(true)
  const attempts=events.filter(e=>e.phase==='houdini-attempt')
  for(const law of [f.left,f.right])expect(attempts.filter(e=>e.law===law.name)).toHaveLength(1)
  expect(attempts.some(e=>e.round===1)).toBe(false)
  expect(events.filter(e=>e.phase==='premise-replay'&&e.retained===true).map(e=>String(e.law)).sort()).toEqual([f.left.name,f.right.name].sort())
  expect(result.proof!.premises?.[f.left.name]).toEqual([f.right.name])
 }finally{countsDump.on=prior}
}))

test('a helper that falls cannot authorize the caller in the following round',()=>withScopes(until=>{
 const f=fixture();f.m.step.state!.right=n(1)
 const prior=countsDump.on,events:Record<string,unknown>[]=[]
 countsDump.on=e=>events.push(e as Record<string,unknown>)
 try{
  const result=admitCountedFamily(f.m,[f.left],[f.left,f.right],new Set(),until)
  expect(result.proven).toBe(false)
  expect(events.some(e=>e.phase==='premise-replay'&&e.law===f.left.name&&e.retained===false)).toBe(true)
  expect(events.some(e=>e.phase==='houdini-attempt'&&e.law===f.left.name&&e.round===1)).toBe(true)
 }finally{countsDump.on=prior}
}))

test('flags off retain legacy carry without premise metadata or replay phases',()=>withScopes(until=>{
 const f=fixture(),prior=countsDump.on,events:Record<string,unknown>[]=[]
 countsDump.on=e=>events.push(e as Record<string,unknown>)
 try{
  const result=admitCountedFamily(f.m,[f.left],f.family,new Set(),until)
  expect(result.proven).toBe(true)
  expect(result.proof).toBeDefined()
  expect(Object.hasOwn(result.proof!,'premises')).toBe(false)
  expect(events.some(e=>e.phase==='premise-replay'||e.phase==='houdini-attempt')).toBe(false)
  expect(checkCountedLaws(result.m,result.laws,result.proof!)).toBe(true)
 }finally{countsDump.on=prior}
},'0'))

// This older lane does not yet carry lane A's complete-work runtime; keep its
// regression intact and explicit until that independently gated runtime lands.
test.skipIf(!('withBudget' in await import('../kernel/prove.ts')))('scope capture and replay consume complete work with both control clocks forbidden',()=>{
 const env=Object.fromEntries(Object.entries(process.env).filter(([name])=>!name.startsWith('GDP_')))
 const child=spawnSync(process.execPath,['--eval',`
  import {strict as assert} from 'node:assert';
  import {scopeCountProof,replayScopedCountProof} from './core/count-proof-scope.ts';
  import {rescopeCountProof} from './core/count-proof-rescope.ts';
  import {countedAttempts} from './core/counts.ts';
  import {withBudget,clock,fullWork,BudgetExpired} from './kernel/prove.ts';
  let reads=0;const forbidden=()=>{reads++;throw Error('raw scope clock')};
  Object.defineProperty(performance,'now',{value:forbidden});Object.defineProperty(Date,'now',{value:forbidden});
  const c=v=>({op:'const',value:v}),v=name=>({op:'var',name});
  const law={name:'kept',holds:{op:'=',a:v('x'),b:c(0)}};
  const m={name:'generic scope clock',params:[],inputs:[],state:{x:c(0)},step:{state:{x:c(0)}}};
  let scoped;const start=fullWork();
  withBudget(500000,()=>{
   const until=clock()+2000,result=countedAttempts(m,[law],new Set(),until).traced(law,[law],0,2000);
   assert('proof' in result);scoped=scopeCountProof(m,law,[law],result.proof,until);assert(scoped);
   assert(replayScopedCountProof(m,[law],scoped,until));
   assert(rescopeCountProof(m,law,[law],result.proof,new Set(),until));
  });
  assert(fullWork()>start);assert.equal(reads,0);
  const atStop=fullWork();let stopped;
  try { stopped=withBudget(0,()=>replayScopedCountProof(m,[law],scoped,Infinity)); }
  catch(error) { assert(error instanceof BudgetExpired); }
  assert.equal(stopped,undefined);assert.equal(fullWork(),atStop);assert.equal(reads,0);
 `],{cwd:new URL('../',import.meta.url).pathname,env:{...env,GDP_WORK_FULL:'1'},encoding:'utf8',timeout:20000})
 if(child.status!==0)throw Error(child.stderr)
 expect(child.status).toBe(0)
})
