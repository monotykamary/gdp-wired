// Run in its OWN Bun process with GDP_WORK_FULL=1 and the default unit fixture
// weights. Only untrusted recipe/shape/proposal production is replaced. The
// public entry, ledger, tickets, scope capture, transport and kernel stay real.
// N3 is intentionally RED until disjoint production segmentation is wired;
// its synthetic work is NOT a measured T301 cost or a production b0 selection.
import {beforeAll,expect,mock,spyOn,test} from 'bun:test'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {admitCountedFamily,countsDump} from './counts.ts'
import * as strategies from './count-strategies.ts'
import * as planning from './count-prerequisite-plan.ts'
import * as liftedShape from './count-lifted-shape.ts'
import * as scope from './count-proof-scope.ts'
import {type CountLawProof,type CountFamilyProof,type ScopedCountProof} from './count-proof-scope.ts'
import {type CountComponentRecipe} from './count-prerequisite-components.ts'
import {type LiftedWorkBudget,liftedWorkLeaseBudget,withLiftedCase} from './count-lifted-budget.ts'
import {countRecipeGraph,type CountRecipeMember} from './count-recipe-graph.ts'
import {workLedger} from './work-admission.ts'
import {workAmount} from './work-amount.ts'
import {completeWorkProfile} from './work-profile.ts'
import {type CountCert,canon,checkCountedLaws,checkMC,countedObligations,leafConstraintsReusing,lemmaPath,mcGoal} from '../kernel/kernel.ts'
import {clock,fullRate,grow,withBudget} from '../kernel/prove.ts'
import {refuteFast} from './solver.ts'

const a=(n:number)=>workAmount(BigInt(n))
const UNIT_ROOT=1_200_000, PUBLIC_ROOT=25_000_000
const controllerPath='./count-recipe-controller.ts'
// Lazy value import keeps public-entry tests executable on the unwired base:
// a missing controller must not prevent every other test from loading.
const controller=()=>import(controllerPath) as Promise<typeof import('./count-recipe-controller.ts')>
beforeAll(()=>{
 expect(completeWorkProfile.enabled).toBe(true)
 expect(workLedger.weights.ticks).toEqual(a(1))
})
function bounded<T>(raw:number,run:()=>T):T{
 // withWall takes counted endpoints inside a work scope, not wall time.
 // The raw root bounds work; Bun/process timeouts bound wall time separately.
 return withBudget(raw,run)
}
function independent(names:readonly string[]){
 const family=names.map((name,i):Law=>({name,holds:same(x('v'+i),n(0))}))
 const values=Object.fromEntries(names.map((_,i)=>['v'+i,n(0)]))
 const m:Machine={name:'section46 native acceptance fixture',params:[],inputs:[],state:values,step:{state:{...values}}}
 return {m,family}
}
function prove(m:Machine,owner:Law,family:Law[]):CountLawProof{
 const instances={},certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(m,family,{[owner.name]:instances},family.indexOf(owner))){
  const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)
  if(!expanded)throw Error('fixture expansion refused: '+goal.name)
  const result=grow(expanded,new Map(),{nodes:0,until:Infinity})
  if(!('tree'in result))throw Error('fixture producer did not close: '+goal.name)
  certs[goal.name]={...base,tree:result.tree}
 }
 return {status:'unchecked',instances,certs,premises:family.map(law=>law.name)}
}
function nativeClose(m:Machine,family:Law[],rows:readonly {id:string,payload:CountLawProof,premises:readonly string[]}[]):CountFamilyProof{
 const proof:CountFamilyProof={instances:{},certs:{},premises:{}}
 for(const row of rows){proof.instances[row.id]=row.payload.instances;Object.assign(proof.certs,row.payload.certs);proof.premises![row.id]=row.premises}
 expect(checkCountedLaws(m,family,proof)).toBe(true)
 return proof
}
function wire(proof:CountFamilyProof){return JSON.stringify({instances:proof.instances,certs:proof.certs,premises:proof.premises})}
function recipe(id:string,required:readonly string[]|undefined):CountComponentRecipe{
 return {id,kind:'strategy',...(required===undefined?{}:{required})}
}
type Fixture={family:Law[],recipes:Map<string,readonly CountComponentRecipe[]>,
 produce:(m:Machine,family:Law[],law:Law,budget?:LiftedWorkBudget)=>CountLawProof|undefined,
 lifted?:ReadonlySet<string>,calls:string[]}
let fixture:Fixture|undefined
const originals={...strategies},planner={...planning},shape={...liftedShape}
void mock.module('./count-strategies.ts',()=>({...originals,
 prepareCountStrategyMachine:(m:Machine)=>m,
 selectedCountStrategies:()=>fixture?.family??[],
 proposeCountStrategyKindForClosing:(_kind:'row'|'guard',m:Machine,family:Law[],law:Law)=>{
  if(!fixture)throw Error('producer called outside a fixture')
  fixture.calls.push(law.name)
  return fixture.produce(m,family,law)
 },
 proposeCountStrategiesForClosing:(m:Machine,family:Law[],law:Law,_until:number,_request:unknown,_observe:unknown,_allowance:unknown,_shape:unknown,budget?:LiftedWorkBudget)=>{
  if(!fixture)throw Error('producer called outside a fixture')
  fixture.calls.push(law.name)
  return fixture.produce(m,family,law,budget)
 }}))
void mock.module('./count-prerequisite-plan.ts',()=>({...planner,countPrerequisiteSchedule:()=>{
 if(!fixture)throw Error('planner called outside a fixture')
 return {requirements:new Map([...fixture.recipes].map(([name,rs])=>[name,rs.flatMap(r=>r.required??[])])),
  recipes:fixture.recipes,costs:new Map(fixture.family.map((law,i)=>[law.name,i]))}
}}))
void mock.module('./count-lifted-shape.ts',()=>({...shape,
 discoverLiftedCountGuard:(m:Machine,law:Law,family:Law[])=>fixture?.lifted?.has(law.name)
  ?({fixture:true} as unknown as NonNullable<ReturnType<typeof shape.discoverLiftedCountGuard>>)
  :shape.discoverLiftedCountGuard(m,law,family),
 discoverLiftedCountOperations:(m:Machine,guard:Parameters<typeof shape.discoverLiftedCountOperations>[1])=>
  (guard as unknown as {fixture?:boolean}).fixture
   ?Array.from({length:7},(_,value)=>({value,name:'op'}))
   :shape.discoverLiftedCountOperations(m,guard)
}))
const flags=['GDP_COUNT_STRATEGIES','GDP_COUNT_TIERS','GDP_COUNT_FINAL_DEFER_CHECKS','GDP_COUNT_CLOSING_RESERVE','GDP_COUNT_PREREQUISITES','GDP_COUNT_PROOF_GUIDED_SCHEDULING']
function publicRun(f:Fixture,m:Machine,caller:Law[],root=PUBLIC_ROOT,after?:(result:ReturnType<typeof admitCountedFamily>)=>void){
 const saved=new Map(flags.map(key=>[key,process.env[key]])),previous=countsDump.on,events:Record<string,unknown>[]=[]
 fixture=f;for(const key of flags)process.env[key]='1'
 countsDump.on=event=>events.push(event as Record<string,unknown>)
 try{
  const result=bounded(root,()=>{
   const out=admitCountedFamily(m,caller,f.family,new Set(),clock()+root/fullRate)
   if(out.proven)expect(checkCountedLaws(out.m,out.laws,out.proof!)).toBe(true)
   after?.(out);return out
  })
  return {result,events,calls:[...f.calls]}
 }finally{
  fixture=undefined;countsDump.on=previous
  for(const [key,value]of saved)if(value===undefined)delete process.env[key];else process.env[key]=value
 }
}
const attempts=(events:Record<string,unknown>[])=>events.filter(e=>e.phase==='count-component-attempt')

test('N1: three different soft keys exhaust, then real native proposal closes with F-3 tickets',async()=>{
 const {CountRecipePass,runCountRecipeController}=await controller()
 bounded(UNIT_ROOT,()=>{
  const {m,family}=independent(['target']),owner=family[0]!,events:Record<string,unknown>[]=[]
  const pass=new CountRecipePass<CountLawProof>([{name:owner.name,reference:0,recipes:[{id:'lifted',kind:'strategy',required:[],caseKeys:['op:0','op:1','op:2']}]}],'same instance')
  const out=runCountRecipeController<CountLawProof,CountFamilyProof,CountLawProof>(pass,[owner.name],{
   observe:event=>events.push(event),
   construct:(_name,_recipe,budget)=>{
    expect(budget?.lease).toBeDefined()
    for(const key of ['op:0','op:1','op:2'])withLiftedCase(Infinity,budget!,false,key,()=>workLedger.start('ticks',60_000))
    return prove(m,owner,family)
   },
   capture:(_name,_recipe,payload)=>({payload,premises:[],checkedReduced:false,checkCost:a(0)}),
   close:rows=>nativeClose(m,family,rows)
  })
  expect(out.result).toBeDefined();expect(attempts(events)).toHaveLength(4)
  expect(events.filter(e=>e.phase==='count-recipe-result'&&e.outcome==='unfinished').map(e=>(e.stop as {key:string}).key)).toEqual(['op:0','op:1','op:2'])
  expect(pass.states[0]!.recipes[0]!.tickets.snapshot()).toMatchObject({started:4,remaining:3,terminal:true})
 })
})

test('N2: retry certificate bytes equal an independently rebuilt larger-first-allowance certificate',async()=>{
 const {CountRecipePass,runCountRecipeController}=await controller()
 const {m,family}=independent(['target']),owner=family[0]!
 const build=(budget:LiftedWorkBudget)=>{
  withLiftedCase(Infinity,budget,false,'op:0',()=>workLedger.start('ticks',60_000))
  return prove(m,owner,family)
 }
 const retry=bounded(UNIT_ROOT,()=>{
  const pass=new CountRecipePass<CountLawProof>([{name:owner.name,reference:0,recipes:[{id:'lifted',kind:'strategy',required:[],caseKeys:['op:0']}]}],'same bytes')
  const out=runCountRecipeController<CountLawProof,CountFamilyProof,CountLawProof>(pass,[owner.name],{construct:(_name,_recipe,budget)=>build(budget!),
   capture:(_name,_recipe,payload)=>({payload,premises:[],checkedReduced:false,checkCost:a(0)}),close:rows=>nativeClose(m,family,rows)})
  expect(pass.states[0]!.recipes[0]!.tickets.snapshot()).toMatchObject({started:2,remaining:5,terminal:true})
  expect(out.result).toBeDefined();return out.result!
 })
 const largerFirst=bounded(UNIT_ROOT,()=>nativeClose(m,family,[{id:owner.name,payload:build(liftedWorkLeaseBudget(a(UNIT_ROOT),{cases:{'op:0':a(80_000)}})),premises:[]}]))
 expect(wire(retry)).toBe(wire(largerFirst))
})

test('N3/46.17: public T301-shaped half retry funds body separately and closes dependents (expected RED while flat)',()=>{
 const {m,family}=independent(['half','Inv*','K3','safety']),[half,inv,k3,target]=family as [Law,Law,Law,Law]
 const rs=new Map<string,readonly CountComponentRecipe[]>([
  [half.name,[recipe('lifted',[])]],[inv.name,[recipe('row',[half.name])]],
  [k3.name,[recipe('row',[half.name,inv.name])]],[target.name,[recipe('row',[half.name,inv.name,k3.name])]]])
 const out=publicRun({family,recipes:rs,lifted:new Set([half.name]),calls:[],produce:(machine,context,law,budget)=>{
  if(law===half){
   expect(budget?.lease).toBeDefined()
   for(let op=0;op<7;op++)withLiftedCase(Infinity,budget!,false,'op:'+op,()=>workLedger.start('ticks',op===0?63_000_000:1))
   // Deliberately outside every case. A flat C+L round cannot pay this;
   // completed body + separate C can. Neither constant is a measured b_min.
   workLedger.start('ticks',297_000_000,'synthetic T301-shaped body')
  }
  return prove(machine,law,context)
 }},m,[target],960_000_000)
 expect(out.result.proven).toBe(true)
 expect(attempts(out.events).filter(e=>e.law===half.name)).toHaveLength(2)
 expect(out.calls).toEqual([half.name,half.name,inv.name,k3.name,target.name])
 expect(out.events.some(e=>e.phase==='count-recipe-result'&&e.outcome==='hard-cap')).toBe(false)
})

test('N4: once the only half route is blocked no dependent attempt or later producer starts',()=>{
 const {m,family}=independent(['half','Inv*','Inv3915','K3','safety']),[half,inv,other,k3,target]=family as [Law,Law,Law,Law,Law]
 const rs=new Map(family.map(law=>[law.name,[recipe('row',law===half?[]:law===target?[half.name,inv.name,other.name,k3.name]:[half.name])]]))
 const out=publicRun({family,recipes:rs,calls:[],produce:(_m,_f,law)=>{if(law!==half)throw Error('blocked dependent producer started');return undefined}},m,[target])
 expect(out.result.proven).toBe(false);expect(out.calls).toEqual([half.name])
 expect(attempts(out.events).map(e=>e.law)).toEqual([half.name])
 const terminal=out.events.findIndex(e=>e.phase==='count-recipe-result'&&e.law===half.name&&e.outcome==='decline')
 expect(terminal).toBeGreaterThanOrEqual(0)
 expect(attempts(out.events.slice(terminal+1))).toHaveLength(0)
})

function addRequiredUnusedCut(m:Machine,owner:Law,context:Law[],dependency:Law,proof:CountLawProof){
 const {goal,decls}=countedObligations(m,context,{[owner.name]:proof.instances},context.indexOf(owner))[1]!
 const cert=proof.certs[goal.name]!,expanded=mcGoal(goal.hyps,decls,cert)!
 const index=goal.hyps.findIndex(h=>JSON.stringify(h)===JSON.stringify(dependency.holds))
 expect(index).toBeGreaterThanOrEqual(0)
 const cut={v2:1,'1':-7},path=new Map([[canon(cut),{lin:cut,holds:false}]])
 const leaf=refuteFast(leafConstraintsReusing({name:'required independent cut',hyps:[goal.hyps[index]!]},path),256)
 if(leaf?.kind!=='refuted')throw Error('cut source fixture failed')
 const lemmas=[{when:[],cut,slice:[index],tree:{leaf:leaf.steps}}]
 const main=grow(expanded,lemmaPath(lemmas,new Map()),{nodes:0,until:Infinity})
 if(!('tree'in main))throw Error('cut-bearing fixture failed')
 proof.certs[goal.name]={...cert,lemmas,tree:main.tree}
 expect(checkMC(goal.hyps,decls,proof.certs[goal.name]!)).toBe(true)
 return proof
}
test('N5: stranded alternative replaces, rather than relabels, the old cut-bearing proof',()=>{
 const {m,family}=independent(['target','replaceable','missing']),[target,member,missing]=family as [Law,Law,Law]
 missing.holds=same(x('v2'),n(7));m.state.v2=n(7);m.step.state!.v2=n(7)
 // The target must really use the member's invariant at STEP. Otherwise a
 // checked reduction can correctly omit this independent member at closing.
 m.step.state!.v0=x('v1')
 let generation=0,oldScope:ScopedCountProof|undefined
 const rs=new Map<string,readonly CountComponentRecipe[]>([[target.name,[recipe('row',[member.name])]],
  [member.name,[recipe('row',[]),recipe('guard',[])]],[missing.name,[recipe('row',[])]]])
 const out=publicRun({family,recipes:rs,calls:[],produce:(machine,context,law)=>{
  if(law===missing)return undefined
  const proof=prove(machine,law,context)
  if(law===member&&generation++===0){
   addRequiredUnusedCut(machine,law,context,missing,proof)
   oldScope=scope.scopeCountProof(machine,law,context,proof,Infinity)
   expect(oldScope?.premises.map(p=>p.name)).toContain(missing.name)
  }
  return proof
 }},m,[target],PUBLIC_ROOT,result=>{
  expect(result.proven).toBe(true);expect(result.laws).not.toContain(missing)
  expect(result.laws).toContain(member)
  expect(oldScope).toBeDefined()
  expect(scope.replayScopedCountProof(m,result.laws,oldScope!,Infinity)).toBeUndefined()
 })
 expect(generation).toBe(2)
 expect(out.calls).toEqual([member.name,missing.name,member.name,target.name])
 const proposals=out.events.filter(e=>e.phase==='count-recipe-result'&&e.law===member.name&&e.outcome==='proposal')
 expect(proposals).toHaveLength(2)
 expect(proposals[0]!.premises).toContain(missing.name)
 expect(proposals[1]!.premises).not.toContain(missing.name)
 expect(out.result.proof?.premises?.[target.name]).toContain(member.name)
 expect(out.result.proof?.premises?.[member.name]).toEqual(proposals[1]!.premises)
 expect(out.result.proof?.premises?.[member.name]).not.toContain(missing.name)
})

test('N6: unchecked understated premises keep known requirements in S and cannot enter G',async()=>{
 const {CountRecipePass,runCountRecipeController}=await controller()
 bounded(UNIT_ROOT,()=>{
  const {m,family}=independent(['target']),owner=family[0]!
  const pass=new CountRecipePass<CountLawProof>([{name:owner.name,reference:0,recipes:[{id:'understated',kind:'strategy',required:['absent']}]}],'understated S')
  const state=pass.states[0]!,r=state.recipes[0]!
  r.terminal=true;state.held={recipeId:r.recipe.id,payload:prove(m,owner,family),premises:[],checkedReduced:false,checkCost:a(0)}
  let closes=0,starts=0
  const out=runCountRecipeController(pass,[owner.name],{construct:()=>{starts++;throw Error('terminal recipe restarted')},close:()=>{closes++;throw Error('unchecked payload admitted to G')}})
  expect(out.reason).toBe('target-blocked');expect(starts).toBe(0);expect(closes).toBe(0)
  const graph=countRecipeGraph([{name:owner.name,reference:0,recipes:[{id:r.recipe.id,required:r.recipe.required,terminal:true}],held:{recipeId:r.recipe.id,premises:[],checkedReduced:false}}],[owner.name],()=>{})
  expect([...graph.requirements.get(owner.name)!]).toEqual(['absent'])
  expect(graph.blocked.has(owner.name)).toBe(true)
 })
})

test('N7: refused reduction keeps funded full-only scope through the public prover and native closing',()=>{
 const {m,family}=independent(['left','right','extra valid scope']),[left,right,extra]=family as [Law,Law,Law]
 m.step.state!.v0=x('v1');m.step.state!.v1=x('v0')
 const rs=new Map(family.map(law=>[law.name,[recipe('row',law===left?[right.name]:law===right?[left.name]:[])]]))
 const replay=spyOn(scope,'replayScopedCountProof');replay.mockImplementationOnce(()=>undefined)
 try{
  const out=publicRun({family,recipes:rs,calls:[],produce:(machine,context,law)=>prove(machine,law,context)},m,[left])
  expect(out.result.proven).toBe(true)
  expect(out.events.some(e=>e.phase==='count-component-rescope'&&e.stage==='canonical'&&e.checked===false)).toBe(true)
  expect(out.events.filter(e=>e.phase==='count-component-rescope'&&e.stage==='original'&&e.checked===true)).toHaveLength(1)
  const fullOnly=out.events.find(e=>e.phase==='count-recipe-result'&&e.outcome==='proposal'&&e.checkedReduced===false)
  expect(fullOnly).toBeDefined();expect(fullOnly!.premises).toContain(extra.name)
  const epochs=out.events.filter(e=>e.phase==='count-rescope-identity').map(e=>e.rootEpoch)
  expect(epochs.length).toBeGreaterThan(0);expect(new Set(epochs).size).toBe(1)
  expect(out.result.proof?.premises?.[fullOnly!.law as string]).toContain(extra.name)
 }finally{replay.mockRestore()}
})

test('N8/46.15: target with only unknown-set recipe considers inventory but invents no premise',()=>{
 const {m,family}=independent(['base','known user','target']),[base,user,target]=family as [Law,Law,Law]
 const rs=new Map<string,readonly CountComponentRecipe[]>([[base.name,[recipe('row',[])]],
  [user.name,[recipe('row',[base.name])]],[target.name,[recipe('row',undefined)]]])
 const out=publicRun({family,recipes:rs,calls:[],produce:(machine,context,law)=>prove(machine,law,context)},m,[target])
 expect(out.result.proven).toBe(true);expect(out.calls).toEqual([base.name,user.name,target.name])
 expect(out.result.proof?.premises?.[target.name]).toEqual([])
 expect(out.result.laws).toEqual([target])
})

test('D1: a selected known recipe becoming ineligible before start cannot borrow its unknown alternative',async()=>{
 const {CountRecipePass,runCountRecipeController}=await controller()
 bounded(UNIT_ROOT,()=>{
  const {m,family}=independent(['target','dependency']),[target,dependency]=family as [Law,Law]
  const pass=new CountRecipePass<CountLawProof>([
   {name:target.name,reference:0,recipes:[{id:'known',kind:'strategy',required:[dependency.name]},{id:'unknown',kind:'strategy'}]},
   {name:dependency.name,reference:1,recipes:[{id:'completed',kind:'strategy',required:[]}]}
  ],'eligibility race')
  const dependencyState=pass.states[1]!,prior=prove(m,dependency,[dependency])
  nativeClose(m,[dependency],[{id:dependency.name,payload:prior,premises:[]}])
  dependencyState.recipes[0]!.terminal=true
  dependencyState.held={payload:prior,premises:[],checkedReduced:true,checkCost:a(0),recipeId:'completed'}
  const events:Record<string,unknown>[]=[],calls:string[]=[]
  let changed=false
  const out=runCountRecipeController<CountLawProof,CountFamilyProof,CountLawProof>(pass,[target.name],{
   observe:event=>{
    events.push(event)
    if(!changed&&event.phase==='count-recipe-admission'&&event.law===target.name&&event.recipe==='known'){
     // The real admission observation is after preparation and before the
     // funded round's eligibility callback. Withdraw the completed dependency;
     // its only recipe is terminal. Target itself remains open via unknown.
     dependencyState.held=undefined;changed=true
    }
   },
   construct:(name,selected)=>{
    calls.push(name+':'+selected.id)
    return selected.id==='known'?undefined:prove(m,target,[target])
   },
   capture:(_name,_selected,payload)=>({payload,premises:[],checkedReduced:false,checkCost:a(0)}),
   close:rows=>nativeClose(m,[target],rows)
  })
  expect(changed).toBe(true);expect(out.result).toBeDefined()
  expect(calls).toEqual([target.name+':unknown'])
  expect(attempts(events).filter(event=>event.recipe==='known')).toHaveLength(0)
  expect(pass.states[0]!.recipes[0]!.tickets.snapshot()).toMatchObject({started:0,remaining:7})
  expect(pass.states[0]!.recipes[1]!.tickets.snapshot()).toMatchObject({started:1,remaining:6,terminal:true})
 })
})

const graphRow=(name:string,reference:number,required:readonly string[]|undefined,terminal=false):CountRecipeMember=>({name,reference,recipes:[{id:'route',required,terminal}]})
test('46.15: known empty differs from unknown; terminal or usable unknown is not an expansion trigger',()=>{
 for(const target of [graphRow('target',0,[]),graphRow('target',0,undefined,true),
  {...graphRow('target',0,undefined,true),held:{recipeId:'route',premises:[],checkedReduced:true}}]){
  const out=countRecipeGraph([target,graphRow('outside',1,[])],['target'],()=>{})
  expect(out.candidates.has('outside')).toBe(false)
 }
})
test('46.15: unknown child widens consideration, recomputes scores, and leaves Req unchanged',()=>{
 const rows=[graphRow('target',9,['child']),graphRow('child',8,undefined),graphRow('base',7,[]),graphRow('known user',1,['base'])]
 for(const order of [rows,[...rows].reverse()]){
  const out=countRecipeGraph(order,['target'],()=>{})
  expect(out.candidates.has('base')).toBe(true);expect(out.next?.name).toBe('base')
  expect([...out.requirements.get('child')!]).toEqual([])
  expect([...out.requirements.get('target')!]).toEqual(['child'])
 }
})
test('46.15: known route blocked by half does not block an eligible unknown alternative',()=>{
 const half=graphRow('half',0,[],true),known={id:'known',required:['half'],terminal:false}
 const blocked=countRecipeGraph([half,{name:'target',reference:1,recipes:[known]}],['target'],()=>{})
 expect(blocked.stop).toBe('target-blocked')
 const open=countRecipeGraph([half,{name:'target',reference:1,recipes:[known,{id:'unknown',terminal:false}]}],['target'],()=>{})
 expect(open.blocked.has('target')).toBe(false);expect(open.next?.recipe.id).toBe('unknown')
})
