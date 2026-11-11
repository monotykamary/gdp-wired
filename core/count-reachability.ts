// Incomplete, untrusted reachable-refutation search. Only the unchanged ledger
// replay on ORIGINAL init/step can reject. No trace, model or finite exhaustion
// can prove a law. No protocol/operation/map/label-specific search templates.
import {type C,type E,type Law,type Machine,type Request,type State,interpret,walk} from './machine.ts'
import {retainedSamplePath,retainedSamples} from './exists.ts'
import {finiteEvaluator} from './finite-houdini.ts'
import {createRejectionStage} from './rejection-stage.ts'
import {countGenerationPhase} from './count-generation-phase.ts'
import {countReachabilityAllowance} from './count-reachability-budget.ts'
import {requestQuotient} from './request-quotient.ts'
import {coreMeter} from './meter.ts'
import {completeWorkProfile} from './work-profile.ts'
import {runtimeWall} from './runtime-wall.ts'
import {reachEdge,reachState,withReachabilityWork} from './work-observe.ts'
import {BudgetExpired,checkBudget,clock,fullRate,keyValue} from '../kernel/prove.ts'
import {WallExpired} from './wall.ts'
type Params=Record<string,number>
export type CountReachabilityModel=Readonly<Record<string,number>>
export type CountReachabilityFunding=Map<string,{grant:number,used:number}>
type Node={p:Params,state:State,path:readonly Request[],depth:number}
export type CountReachabilityReceipt={law:string,stage:'not-required'|'samples'|'model'|'frontier',outcome:'not-required'|'no-witness'|'exhausted'|'rejected'|'broken',granted:number,used:number,incomplete:true,phases:{stage:string,used:number,complete:boolean}[],maxSize:number,maxDepth:number}
function tick():void{
 checkBudget('reachable screen')
 if(completeWorkProfile.enabled){runtimeWall.admit?.(completeWorkProfile.weights.ticks,'reachable bookkeeping');coreMeter.ticks++}
}
const natural=(x:unknown):x is number=>typeof x==='number'&&Number.isSafeInteger(x)&&x>=0
const atoms=(c:C):C[]=>c.op==='and'?c.xs.flatMap(atoms):[c]
// Lazy scalar/product/set enumeration. Irrelevant fields may be held at zero
// only when the existing source analysis supports it; guard inputs stay live.
function* requests(m:Machine,p:Params,size:number):Generator<Request>{
 const tags=new Map<string,Set<number>>(),guard=new Set<string>()
 walk(m.step,o=>{tick();if(o.op==='='&&o.a&&o.b){const a=o.a as E,b=o.b as E,v=a.op==='var'?a:b,k=a.op==='var'?b:a;if(v.op==='var'&&k.op==='const'&&m.inputs.includes(v.name)&&natural(k.value)){let set=tags.get(v.name);if(!set)tags.set(v.name,set=new Set());set.add(k.value)}}})
 if(m.assume)walk(m.assume,o=>{tick();if(o.op==='var')guard.add(String(o.name));if(o.op==='get')guard.add(String(o.map))})
 const domain=(name:string):number[]=>{
  let bound=size
  for(const c of m.assume?atoms(m.assume):[])if((c.op==='<'||c.op==='<=')&&c.a.op==='var'&&c.a.name===name){const k=c.b.op==='const'?c.b.value:c.b.op==='var'?p[c.b.name]:undefined;if(natural(k))bound=Math.min(bound,k+(c.op==='<='?1:0))}
  const values=new Set<number>();for(let i=0;i<bound;i++){tick();values.add(i)}
  for(const x of tags.get(name)??[]){tick();values.add(x)}
  return [...values]
 }
 const names=[...m.inputs,...m.inputMaps??[]],base:Request=Object.fromEntries(names.map(name=>[name,m.inputs.includes(name)?0:new Map<number,number>()]))
 const selector=[...tags].filter(([,vs])=>vs.size>1).sort((a,b)=>b[1].size-a[1].size||m.inputs.indexOf(a[0])-m.inputs.indexOf(b[0]))[0]?.[0]
 const values=selector?domain(selector):[undefined]
 const seeds=values.flatMap(value=>{const r={...base,...selector?{[selector]:value!}:{}};return [r,r]})
 const quotient=seeds.length?requestQuotient(m,seeds):undefined
 function* product(fields:readonly string[],at:number,r:Request):Generator<Request>{
  tick();if(at===fields.length){yield r;return}
  const name=fields[at]!
  if(m.inputs.includes(name)){for(const value of domain(name))yield* product(fields,at+1,{...r,[name]:value});return}
  const bits:boolean[]=[];for(let i=0;i<size;i++){tick();bits.push(false)}
  for(;;){
   tick();const cells=new Map<number,number>();for(let i=0;i<bits.length;i++){tick();if(bits[i])cells.set(i,1)}
   yield* product(fields,at+1,{...r,[name]:cells})
   let i=0;for(;i<bits.length&&bits[i];i++){tick();bits[i]=false}if(i===bits.length)break;bits[i]=true
  }
 }
 for(const value of values){
  tick();const projected=quotient?.selector===selector?quotient?.reads.get(value):undefined
  const live=projected?names.filter(name=>name!==selector&&(projected.includes(name)||guard.has(name))):names.filter(name=>name!==selector)
  yield* product(live,0,{...base,...selector?{[selector]:value!}:{}})
 }
}
function tightLaw(law:Law):Law{
 const tighten=(c:C):C=>{tick();return c.op==='and'||c.op==='or'?{...c,xs:c.xs.map(tighten)}:c.op==='not'?{...c,x:tighten(c.x)}:c.op==='all'?{...c,c:tighten(c.c)}:c.op==='<='?{...c,op:'<'}:c}
 return {...law,holds:tighten(law.holds)}
}
export function countReachabilityScreen(source:Machine,m:Machine,caller:readonly Law[],root:number,samplesHint?:()=>readonly {p:Params,sts:readonly State[]}[],funding:CountReachabilityFunding=new Map()){
 const ledger=createRejectionStage(source,m,caller,[],root),evaluate=finiteEvaluator(m),run=interpret(source,tick),receipts=new Map<Law,CountReachabilityReceipt>()
 const seedSamples=()=>samplesHint?.()??(retainedSamples(source).length?retainedSamples(source):retainedSamples(m))
 const replay=(law:Law,node:Node):boolean=>{
  tick();if(evaluate(law,node.p,node.state)!==false)return false
  // The candidate state's origin is never trusted, even when it was cached.
  // Publication is atomic inside the existing rejection ledger.
  ledger.reachable(node.p,node.path)
  return !!ledger.safety()||!ledger.active().includes(law)
 }
 const step=(node:Node,request:Request):Node|undefined=>{
  tick();try{reachEdge();const state=run.step(node.p,node.state,request);reachState();const path:Request[]=[];for(const r of node.path){tick();path.push(r)}path.push(request);return {p:node.p,state,path,depth:node.depth+1}}
  catch(error){if(error instanceof BudgetExpired||error instanceof WallExpired)throw error;return undefined}
 }
 const initial=(p:Params):Node|undefined=>{tick();try{reachState();return {p,state:run.init(p),path:[],depth:0}}catch(error){if(error instanceof BudgetExpired||error instanceof WallExpired)throw error;return undefined}}
 function screen(law:Law,ordinary:number,citing:number,until:number,model?:CountReachabilityModel):CountReachabilityReceipt{
  checkBudget('reachable promotion parent')
  const previous=receipts.get(law);if(previous)return previous
  ledger.addCandidates([law])
  // Names are unique within a request. A changed/reordered body with the
  // same name may lose reuse, but must never earn another search grant.
  const key=law.name,fund=funding.get(key)??{grant:countReachabilityAllowance(root,ordinary,citing),used:0};funding.set(key,fund)
  const grant=Math.max(0,fund.grant-fund.used),start=clock(),end=Math.min(until,start+grant)
  const row:CountReachabilityReceipt={law:law.name,stage:'samples',outcome:'no-witness',granted:Math.max(0,end-start)*fullRate,used:0,incomplete:true,phases:[],maxSize:0,maxDepth:0}
  receipts.set(law,row)
  let found=false
  const seen=(node:Node)=>{row.maxSize=Math.max(row.maxSize,...Object.values(node.p),0);row.maxDepth=Math.max(row.maxDepth,node.depth);return found=replay(law,node)}
  const phase=(stage:CountReachabilityReceipt['stage'],allowance:number,body:()=>void)=>{
   if(found||clock()>=end)return
   row.stage=stage;const before=clock(),result=countGenerationPhase(Math.min(end,before+allowance),()=>withReachabilityWork(body))
   row.phases.push({stage,used:(clock()-before)*fullRate,complete:result.complete});if(!result.complete)row.outcome='exhausted'
  }
  try{
   const samples=seedSamples()
   phase('samples',Math.min(root/1000,grant/3),()=>{
    const tight=tightLaw(law)
    type Seed={p:Params,state:State,node?:Node,iter?:Generator<Request>}
    const priority:Seed[]=[],other:Seed[]=[]
    for(const {p,sts}of samples)for(const state of sts){
     tick();if(evaluate(law,p,state)===false){const path=retainedSamplePath(state,tick);if(path&&seen({p,state,path,depth:path.length}))return}
     // Evaluate tightness before reconstructing long paths. Non-tight samples
     // must not consume the entire cheap phase's allowance in path copies.
     ;(evaluate(tight,p,state)===false?priority:other).push({p,state})
    }
    let frontier:Seed[]=[...priority,...other]
    for(let depth=0;depth<2;depth++){
     const children:Seed[]=[]
     while(frontier.length){const next:Seed[]=[];for(const item of frontier){
      tick();if(!item.node){const path=retainedSamplePath(item.state,tick);if(!path)continue;item.node={p:item.p,state:item.state,path,depth:path.length}}
      item.iter??=requests(source,item.p,Math.max(1,...Object.values(item.p),3))
      const r=item.iter.next();if(r.done)continue;next.push(item);const child=step(item.node,r.value);if(child){if(seen(child))return;children.push({...child,node:child})}
     }frontier=next}
     frontier=children
    }
   })
   phase('model',Math.max(0,end-clock())/3,()=>{
    if(!model)return
    const p=Object.fromEntries(source.params.map(name=>[name,model[name]??0]));if(!Object.values(p).every(natural))return
    const request:Request=Object.fromEntries(source.inputs.map(name=>[name,model[name]??0]));for(const name of source.inputMaps??[])request[name]=new Map<number,number>()
    for(const [name,value]of Object.entries(model)){tick();const bracket=name.indexOf('['),map=request[name.slice(0,bracket)];if(bracket>=0&&name.endsWith(']')&&map instanceof Map){const k=keyValue(name,model);if(natural(k)&&natural(value))map.set(k,value)}}
    const roots:Node[]=[];const init=initial(p);if(init)roots.push(init)
    for(const sample of samples)if(source.params.every(name=>sample.p[name]===p[name]))for(const state of sample.sts){tick();if(Object.keys(source.state).some(name=>model[name]!==undefined&&state.scalars[name]!==model[name]))continue;const path=retainedSamplePath(state,tick);if(path)roots.push({p,state,path,depth:path.length})}
    for(const node of roots){tick();if(seen(node))return;const child=step(node,request);if(child&&seen(child))return}
   })
   phase('frontier',Math.max(0,end-clock()),()=>{
    type Lane={queue:Node[],keys:Set<string>,at:number,iter?:Generator<Request>}
    const signature=(state:State)=>JSON.stringify(state,(_key,value:unknown)=>{tick();return value instanceof Map?[...value].sort((a:[number,number],b:[number,number])=>{tick();return a[0]-b[0]}):value})
    const lanes:Lane[]=[],params=new Set<string>()
    const add=(p:Params)=>{tick();const key=JSON.stringify(p);if(params.has(key))return;params.add(key);const node=initial(p);if(node){if(seen(node))return;lanes.push({queue:[node],keys:new Set([signature(node.state)]),at:0})}}
    if(model)add(Object.fromEntries(source.params.map(name=>[name,model[name]??0])))
    for(let size=1;!found;size++){
     tick();if(!source.params.length&&size>1&&lanes.every(l=>l.at>=l.queue.length))break
     add(Object.fromEntries(source.params.map(name=>[name,size])))
     for(const lane of lanes)for(let work=0;work<64&&!found;work++){
      tick();const node=lane.queue[lane.at];if(!node)break
      lane.iter??=requests(source,node.p,Math.max(size,...Object.values(node.p),1))
      const r=lane.iter.next();if(r.done){lane.iter=undefined;lane.at++;continue}
      const child=step(node,r.value);if(child){if(seen(child))return;const key=signature(child.state);if(!lane.keys.has(key)){lane.keys.add(key);lane.queue.push(child)}}
     }
    }
   })
   if(found)row.outcome=ledger.safety()==='broken'?'broken':'rejected'
   else if(clock()>=end)row.outcome='exhausted'
   return row
  }finally{const spent=clock()-start;fund.used+=spent;row.used=spent*fullRate}
 }
 return {screen,evidence:ledger.evidence,rejected:()=>ledger.evidence().filter(e=>e.kind==='reachable').map(e=>e.law),safety:ledger.safety,
  receipts:(laws:readonly Law[])=>laws.map(law=>({...receipts.get(law)??{law:law.name,stage:'not-required' as const,outcome:'not-required' as const,granted:0,used:0,incomplete:true as const,phases:[],maxSize:0,maxDepth:0},cumulativeUsed:(funding.get(law.name)?.used??0)*fullRate}))}
}
