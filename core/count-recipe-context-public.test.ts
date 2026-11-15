// B independent public G1/G2 controls. MUST run alone in a fresh FULL-profile
// Bun process: the only module replacements are untrusted inventory/proposal
// production. Public admission, scope capture/replay and native checking stay real.
import {beforeAll,expect,mock,test} from 'bun:test'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {admitCountedFamily,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import {type CountComponentRecipe} from './count-prerequisite-components.ts'
import {type CountLawProof} from './count-proof-scope.ts'
import {CountRecipeContexts,countRecipeContextDecision,countRecipeContextSnapshot,countRecipeContextDifference} from './count-recipe-context.ts'
import {CountRecipePass} from './count-recipe-controller.ts'
import {workKeys} from './work-kinds.ts'
import {type ExactRaw,workAmount,workFromExact,workShare,compareWork} from './work-amount.ts'
import {workLedger} from './work-admission.ts'
import {completeWorkProfile} from './work-profile.ts'
import {type CountCert,checkCountedLaws,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,fullRate,grow,withBudget} from '../kernel/prove.ts'
const ROOT=25_000_000,a=(n:number)=>workAmount(BigInt(n))
type Event=Record<string,unknown>
type Fixture={m:Machine,family:Law[],selected:Law[],recipes:Map<string,readonly CountComponentRecipe[]>,calls:string[],decline:boolean,afterFirst?:(event:Event)=>void}
let fixture:Fixture|undefined
const producer={...strategies},planner={...planning}
function proof(m:Machine,family:Law[],owner:Law):CountLawProof{
 const certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:{}},family.indexOf(owner))){
  const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)
  if(!expanded)throw Error('native fixture expansion refused')
  const result=grow(expanded,new Map(),{nodes:0,until:Infinity})
  if(!('tree'in result))throw Error('native fixture did not prove '+goal.name)
  certs[goal.name]={...base,tree:result.tree}
 }
 return {status:'unchecked',instances:{},certs,premises:family.map(l=>l.name)}
}
function propose(kind:'row'|'guard',m:Machine,family:Law[],law:Law){
 if(!fixture)throw Error('proposal outside fixture')
 fixture.calls.push(law.name+':'+kind)
 return fixture.decline?undefined:proof(m,family,law)
}
void mock.module('./count-strategies.ts',()=>({...producer,prepareCountStrategyMachine:(m:Machine)=>m,
 selectedCountStrategies:()=>fixture?.selected??[],proposeCountStrategyKindForClosing:propose,proveCountStrategyKind:propose}))
void mock.module('./count-prerequisite-plan.ts',()=>({...planner,countPrerequisiteSchedule:(_m:Machine,family:Law[])=>{
 if(!fixture)throw Error('inventory outside fixture')
 return {requirements:new Map(family.map(l=>[l.name,(fixture!.recipes.get(l.name)??[]).flatMap(r=>r.required??[])])),
  recipes:new Map(family.map(l=>[l.name,fixture!.recipes.get(l.name)??[]])),costs:new Map(family.map((l,i)=>[l.name,i]))}
}}))
beforeAll(()=>{expect(completeWorkProfile.enabled).toBe(true);expect(workLedger.weights.ticks).toEqual(a(1))})
function independent(names:string[]){
 const family=names.map((name,i):Law=>({name,holds:same(x('v'+i),n(0))}))
 const state=Object.fromEntries(names.map((_,i)=>['v'+i,n(0)]))
 const m:Machine={name:'B native G controls',params:[],inputs:[],state,step:{state:{...state}}}
 return {m,family}
}
const flags=['GDP_COUNT_STRATEGIES','GDP_COUNT_TIERS','GDP_COUNT_FINAL_DEFER_CHECKS','GDP_COUNT_CLOSING_RESERVE','GDP_COUNT_PREREQUISITES','GDP_COUNT_PROOF_GUIDED_SCHEDULING']
function run(f:Fixture,caller:Law[]){
 const saved=new Map([...flags,'GDP_COUNT_REACHABILITY_SCREEN'].map(k=>[k,process.env[k]])),prior=countsDump.on,events:Event[]=[],start=countRecipeContextSnapshot()
 fixture=f;for(const key of flags)process.env[key]='1';process.env.GDP_COUNT_REACHABILITY_SCREEN='0'
 countsDump.on=event=>{const row=event as Event;events.push(row);f.afterFirst?.(row)}
 try{
  const result=withBudget(ROOT,()=>{
   const out=admitCountedFamily(f.m,caller,f.family,new Set(),clock()+ROOT/fullRate)
   if(out.proven)expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
   return out
  })
  return {result,events,delta:countRecipeContextDifference(countRecipeContextSnapshot(),start),calls:[...f.calls]}
 }finally{fixture=undefined;countsDump.on=prior;for(const [key,value]of saved)if(value===undefined)delete process.env[key];else process.env[key]=value}
}
function single(decline:boolean):Fixture{
 const {m,family}=independent(['target'])
 return {m,family,selected:family,recipes:new Map([['target',[{id:'row',kind:'strategy',required:[]}]]]),calls:[],decline}
}

test('G1 public: widened ordinary supporter uses Q plus itself and still closes through the native checker',()=>{
 const {m,family}=independent(['base','user','target',...Array.from({length:20},(_,i)=>'outside'+i)]),target=family[2]!
 const recipes=new Map<string,readonly CountComponentRecipe[]>(family.map((law,i)=>[law.name,[i===2?{id:'row',kind:'strategy' as const}:{id:'ordinary',kind:'ordinary' as const,required:i===1?['base']:[]}]]))
 const out=run({m,family,selected:[target],recipes,calls:[],decline:false},[target])
 const first=out.events.find(e=>e.phase==='count-recipe-admission'&&e.law==='base')
 expect(first).toBeDefined()
 const allotted=workFromExact(first!.allotted as ExactRaw)
 // Old widened pending-count policy fails this numerical bound before any
 // new event-field assertion. The target-only closure plus base gives p=2.
 expect(compareWork(allotted,a(ROOT/10))).toBeGreaterThan(0)
 expect(first!.allocationCohort).toBe(2)
 expect(allotted).toEqual(workShare(workFromExact(first!.allocationRemaining as ExactRaw),1n,2n))
 expect(out.result.proven).toBe(true);expect(out.result.proof).toBeDefined()
 expect(out.delta).toEqual({contextChanges:0,structuredReentries:0,terminalStructuredReentries:0})
})

test('G2 public: changed model bytes get a fresh pass and the true core proves on fallback',()=>{
 const f=single(true);let changed=false
 f.afterFirst=event=>{if(!changed&&event.phase==='count-recipe-closing'){f.m.name+=' changed context';f.decline=false;changed=true}}
 const out=run(f,f.family)
 expect(changed).toBe(true);expect(out.result.proven).toBe(true)
 expect(checkCountedLaws(out.result.m,out.result.laws,out.result.proof!)).toBe(true)
 expect(out.calls).toEqual(['target:row','target:row'])
 expect(out.events.filter(e=>e.phase==='count-component-attempt')).toHaveLength(2)
 expect(out.events.filter(e=>e.phase==='count-recipe-context')).toEqual([])
 expect(out.delta).toEqual({contextChanges:0,structuredReentries:0,terminalStructuredReentries:0})
})

test('G2 public: same-context structured fallback reports terminal inventory without repeating construction',()=>{
 const f=single(true),out=run(f,f.family)
 expect(out.result.proven).toBe(false);expect(out.calls).toEqual(['target:row'])
 expect(out.events.filter(e=>e.phase==='count-component-attempt')).toHaveLength(1)
 expect(out.events.filter(e=>e.phase==='count-recipe-context')).toEqual([
  {phase:'count-recipe-context',outcome:'reused',reason:'same-inventory-structured-reentry',structured:true,previousStructured:false,terminalRecipes:1,totalRecipes:1}])
 expect(out.delta).toEqual({contextChanges:0,structuredReentries:1,terminalStructuredReentries:1})
})

test('G2 public: zero-context-event reuse keeps all 26 counters byte-identical to the single-pass path',()=>{
 const context='same',members=[{name:'target',reference:0,recipes:[{id:'row',kind:'strategy' as const}]}]
 const measure=(registry:boolean)=>withBudget(ROOT,()=>{
  const start=workLedger.snapshot(),contexts=new CountRecipeContexts<CountRecipePass<unknown>>()
  let pass:CountRecipePass<unknown>|undefined
  for(let i=0;i<3;i++){
   if(registry)pass=contexts.acquire(context,false,()=>new CountRecipePass(members,context))
   else if(pass){workLedger.start('tableCells',Math.min(context.length,pass.context.length),'count recipe inventory context');expect(countRecipeContextDecision(pass,context,false,false)).toBe(true)}
   else pass=new CountRecipePass(members,context)
  }
  const end=workLedger.snapshot();return Object.fromEntries(workKeys.map(key=>[key,String(BigInt(end.counters[key])-BigInt(start.counters[key]))]))
 })
 expect(measure(true)).toEqual(measure(false))
})
test('G2 public positive: an accepted native proof has no context refusal or structured re-entry',()=>{
 const f=single(false),out=run(f,f.family)
 expect(out.result.proven).toBe(true);expect(out.result.proof).toBeDefined();expect(out.calls).toEqual(['target:row'])
 expect(out.events.filter(e=>e.phase==='count-recipe-context')).toHaveLength(0)
 expect(out.delta).toEqual({contextChanges:0,structuredReentries:0,terminalStructuredReentries:0})
})
