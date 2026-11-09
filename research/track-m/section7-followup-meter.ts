// Post-timing provenance/repetition audit. During proofs retain references only.
import {createHash} from 'node:crypto'
import type {C} from '../../core/machine.ts'
import type {Goal,LemmaCut,Path,Tree} from '../../kernel/kernel.ts'
type Origin={goal:Goal,source:number,reads:number,witnesses:string[]}
type Context={goal:Goal,tree:Tree,path:Path,lemmas:LemmaCut[]}
type Call={goal:Goal,tree:Tree,path:Path,context?:Context}
type Snapshot={label:string,origins:Origin[],calls:Call[]}
const digest=(value:unknown)=>createHash('sha256').update(JSON.stringify(value)).digest('hex')
const repeats=(keys:string[])=>{const frequencies=new Map<string,number>();for(const key of keys)frequencies.set(key,(frequencies.get(key)??0)+1);const repeated=[...frequencies.values()].filter(n=>n>1);return {calls:keys.length,distinct:frequencies.size,repeatedLeaves:repeated.length,callsOnRepeatedLeaves:repeated.reduce((a,b)=>a+b,0),extraChecks:repeated.reduce((a,b)=>a+b-1,0),multiplicities:repeated.sort((a,b)=>b-a)}}
export class FollowupMeter{
 enabled=process.env.LAB_SECTION7_FOLLOWUP==='1'
 private current:Snapshot={label:'',origins:[],calls:[]}
 private saved:Snapshot[]=[]
 private context?:Context
 reset(label:string){if(!this.enabled)return;this.current={label,origins:[],calls:[]}}
 noteGoal<T extends Goal|undefined>(args:any[],goal:T):T{if(this.enabled&&goal)this.current.origins.push({goal,source:args[0].length,reads:args[2].reads.length,witnesses:args[2].insts.map((q:any)=>q.wit)});return goal}
 withLeafContext<T>(goal:Goal,tree:Tree,path:Path,lemmas:LemmaCut[],f:()=>T):T{if(!this.enabled)return f();const old=this.context;this.context={goal,tree,path,lemmas};try{return f()}finally{this.context=old}}
 record(args:any[],caller:string){if(this.enabled&&caller.endsWith('conditional-proof.ts:checked')&&args[0]?.hyps?.length>=400&&args[1]&&'leaf'in args[1])this.current.calls.push({goal:args[0],tree:args[1],path:args[2],context:this.context})}
 seal(){if(!this.enabled)return;this.saved.push(this.current);this.current={label:'',origins:[],calls:[]}}
 audits(){return this.saved.map(s=>this.audit(s))}
 private audit(s:Snapshot){
  const start=performance.now(),kinds=new WeakMap<object,string>(),byText=new Map<string,Set<string>>(),witnesses=new Set(s.origins.flatMap(o=>o.witnesses))
  const mark=(c:C,kind:string)=>{kinds.set(c,kind);const text=JSON.stringify(c),set=byText.get(text)??new Set<string>();set.add(kind);byText.set(text,set)}
  for(const o of s.origins){
   const offset=o.goal.hyps.length-o.witnesses.length
   o.goal.hyps.forEach((c,i)=>{if(i>=offset)mark(c,o.witnesses[i-offset]!.startsWith('frame$')?'frame-count-clause':'other-count-clause');else if(i>=o.source+o.reads)mark(c,'pick-clause');else if(i>=o.source)mark(c,'read-binding');else if(!kinds.has(c))mark(c,'obligation')})
  }
  const ids=new WeakMap<object,number>();let next=0;const id=(o:object)=>{let n=ids.get(o);if(n===undefined){n=++next;ids.set(o,n)}return n}
  const hashes=new WeakMap<object,string>(),hash=(o:object)=>{let h=hashes.get(o);if(!h){h=digest(o);hashes.set(o,h)}return h}
  const provenance=new WeakMap<object,Record<string,number>>()
  const classify=(hyps:C[])=>{let out=provenance.get(hyps);if(out)return out;out={};for(const c of hyps){const choices=byText.get(JSON.stringify(c)),kind=kinds.get(c)??(choices?.size===1?[...choices][0]!:'unclassified');out[kind]=(out[kind]??0)+1}provenance.set(hyps,out);return out}
  const sourceWitnessCounts=(hyps:C[])=>{let source=0,frame=0;for(const c of hyps){if(kinds.get(c)!=='obligation')continue;let has=false,hasFrame=false;const visit=(v:any):void=>{if(!v||typeof v!=='object')return;if(v.op==='var'&&witnesses.has(v.name)){has=true;if(v.name.startsWith('frame$'))hasFrame=true}for(const child of Object.values(v))if(Array.isArray(child))child.forEach(visit);else if(child&&typeof child==='object')visit(child)};visit(c);if(has)source++;if(hasFrame)frame++}return {sourceWitnessBearing:source,sourceFrameWitnessBearing:frame}}
  const rows=s.calls.map((c,i)=>{const goalHash=hash(c.goal.hyps),treeHash=hash(c.tree),pathHash=digest([...c.path]),base=c.context?.path,lemmas=c.context?.lemmas??[],origin=classify(c.goal.hyps);return {call:i+1,goalId:id(c.goal.hyps),treeId:id(c.tree),hyps:c.goal.hyps.length,provenance:origin,...sourceWitnessCounts(c.goal.hyps),goalHash,treeHash,pathHash,problemHash:digest([goalHash,pathHash]),exactHash:digest([goalHash,pathHash,treeHash]),baseScopeAtoms:base?.size,checkedScopeAtoms:c.path.size,additionalScopeAtoms:base?c.path.size-base.size:undefined,regionLemmas:lemmas.length,regionCuts:lemmas.map(l=>l.cut)}})
  const classes=new Map<string,{hyps:number,provenance:Record<string,number>,sourceWitnessBearing:number,sourceFrameWitnessBearing:number,calls:number}>()
  for(const row of rows){const key=JSON.stringify([row.hyps,row.provenance,row.sourceWitnessBearing,row.sourceFrameWitnessBearing]),old=classes.get(key);if(old)old.calls++;else classes.set(key,{hyps:row.hyps,provenance:row.provenance,sourceWitnessBearing:row.sourceWitnessBearing,sourceFrameWitnessBearing:row.sourceFrameWitnessBearing,calls:1})}
  return {test:'section7-followup-leaves',law:s.label,calls:rows.length,provenance:[...classes.values()],sameTreeObject:repeats(rows.map(r=>String(r.treeId))),sameGoalAndTreeObject:repeats(rows.map(r=>`${r.goalId}/${r.treeId}`)),sameExactCheckedLeaf:repeats(rows.map(r=>r.exactHash)),sameProblem:repeats(rows.map(r=>r.problemHash)),sameCertificate:repeats(rows.map(r=>r.treeHash)),rows,auditWallMs:performance.now()-start}
 }
}
export const followup=new FollowupMeter()
