// In-memory observation only. Proof checking/transport happens after search.
import {type Goal,type Path,type Tree,canon,canonFlip,columnTerm,leafConstraints,check,linear,lemmaPath} from '../../kernel/kernel.ts'
import {type C} from '../../core/machine.ts'
import {sub} from '../../core/solver.ts'
import {fullWork,fullRate} from '../../kernel/prove.ts'
import {checkConditionalProof} from '../../core/count-recovery/conditional-proof.ts'
import {admitConditionalCut} from '../../core/count-recovery/conditional-cuts.ts'
import {normalize,dependence,independent} from './section18-data.ts'
const now=()=>fullWork()/fullRate
export type Frame={id:number,parent?:number,kind:string,name:string,start:number,end?:number,units?:number,children:number,exclusive?:number,phase?:string,outcome?:string,meta:any,data?:any}
const copyPath=(p:Path|undefined)=>new Map(p??[])
const proofPath=(when:any[],cut:any):Path=>{const p:Path=new Map();let n=0;for(const a of [{lin:cut,holds:false},...when.map(lin=>({lin,holds:true}))]){const k=canon(a.lin);p.set(p.has(k)?'@'+n++:k,a)}return p}
// Read every used row, including path lookups used while flattening hypotheses.
export function dependencies(goal:Goal,tree:Tree,path:Path,marks:(tree:Tree)=>any=()=>undefined){
 const facts=new Set<number>(),atoms=new Set<string>(),original=new Map(path)
 class Observed extends Map<string,{lin:Record<string,number>,holds:boolean}> {constructor(p:Path){super(p)}override get(k:any){atoms.add(k);return super.get(k)}override has(k:any){atoms.add(k);return super.has(k)}}
 const visit=(t:Tree,p:Path,context:any={goal,lemmas:[]})=>{const own=marks(t);if(own){context=own;for(const lemma of own.lemmas){const slice=lemma.slice??own.goal.hyps.map((_:any,i:number)=>i),local={...own.goal,hyps:slice.map((i:number)=>own.goal.hyps[i])},used=dependencies(local,lemma.tree,proofPath(lemma.when,lemma.cut));for(const i of used.indices)facts.add(slice[i]);for(const condition of lemma.when){const k=canon(condition);atoms.add(k);atoms.add(canonFlip(condition))}}}if('split'in t){const k=canon(t.split);visit(t.yes,new Map(p).set(k,{lin:t.split,holds:true}),context);visit(t.no,new Map(p).set(k,{lin:t.split,holds:false}),context);return}
  const active=lemmaPath(context.lemmas,new Observed(p)),rows=leafConstraints(context.goal,new Observed(active)),values=[...active.values()],mark=(i:number):void=>{if(i>=rows.length+(t.squares?.length??0)){const pair=t.products?.[i-rows.length-(t.squares?.length??0)];if(pair){mark(pair[0]);mark(pair[1])}return}const s=rows[i]?.src;if(s&&'fact'in s)facts.add(s.fact);if(s&&'atom'in s){const a=values[s.atom];if(a)atoms.add(canon(a.lin))}}
  for(const x of t.leaf)if(x.kind==='input')mark(x.index)
 };visit(tree,path);return {indices:[...facts].sort((a,b)=>a-b),atoms:[...original].filter(([k])=>atoms.has(k)).map(([,a])=>a)}
}
class Recorder {
 enabled=true;phase='initial';marks=new WeakMap<Tree,any>();frames:Frame[]=[];stack:Frame[]=[];roots:Goal[]=[];machine:any;law='';op=0
 reset(m:any,law:string,op:number,enabled=true){this.enabled=enabled;this.frames=[];this.stack=[];this.roots=[];this.machine=m;this.law=law;this.op=op;this.marks=new WeakMap()}
 noteMark(tree:Tree,context:any){if(this.enabled)this.marks.set(tree,context)}
 conditions(lin:Record<string,number>):C{return {op:'<=',a:linearExpr(lin),b:{op:'const',value:0}}}
 probe(name:string,good:C,goal:Goal,path:Path,run:()=>Tree|undefined){const a=this.attempt(name,good);try{const tree=run();this.mark(a,{source:goal,sourceTree:tree,sourcePath:path,target:goal,tree,targetPath:path});return tree}finally{this.end(a)}}
 snapshots(tree:Tree|undefined){const out:any[]=[];const visit=(t:Tree,p:string[])=>{const mark=this.marks.get(t);if(mark)out.push({path:p,...mark});if('split'in t){visit(t.yes,[...p,'yes']);visit(t.no,[...p,'no'])}};if(tree)visit(tree,[]);return out}
 root(g:Goal){if(this.enabled&&!this.roots.includes(g))this.roots.push(g)}
 begin(kind:string,name:string,meta:any={}):Frame|undefined{if(!this.enabled)return;const f:Frame={id:this.frames.length,parent:this.stack.at(-1)?.id,kind,name,start:now(),children:0,meta};this.frames.push(f);this.stack.push(f);return f}
 end(f:Frame|undefined){if(!f)return;if(this.stack.pop()!==f)throw Error('lemma ledger stack mismatch');f.end=now();f.units=f.end-f.start;f.exclusive=f.units-f.children;const p=this.stack.at(-1);if(p)p.children+=f.units}
 helper<T>(name:string,args:any[],run:()=>T):T{if(!this.enabled)return run();const field=name==='field',g=args[field?2:0],cert=args[field?3:1],root=args[field?7:4],f=this.begin('helper',name,{goal:g,cert:{reads:[...cert.reads],insts:[...cert.insts]},path:copyPath(root),phase:this.phase});try{return run()}finally{this.end(f)}}
 attempt(name:string,good:C,extra:any={}):Frame|undefined{if(!this.enabled)return;const h=[...this.stack].reverse().find(f=>f.kind==='helper');if(!h)return;return this.begin('attempt',name,{good,helper:h?.id,...extra})}
 mark(f:Frame|undefined,data:any){if(f)f.data={...data,sourcePath:copyPath(data.sourcePath),targetPath:copyPath(data.targetPath)}}
 admitted(data:any){const a=[...this.stack].reverse().find(f=>f.kind==='attempt');this.mark(a,{...data,source:data.part,sourceTree:data.tree,sourcePath:data.from,target:data.g,tree:data.lemma.tree,targetPath:proofPath(data.lemma.when,data.lemma.cut),admitted:true})}
 invoke<T extends (...args:any[])=>any>(name:string,fn:T,args:Parameters<T>):ReturnType<T>{if(!this.enabled||!this.stack.length)return fn(...args);const transport=['widen','liftCountProxies','admitConditionalCut','inlineConditionalCuts','transportConditionalProof'].includes(name),checking=['check','checkConditionalProof'].includes(name),source=['seq','query','grow','booleanCore','refuteFast','fieldCase','proveNaturalCases'].includes(name),f=this.begin('operation',name)!;f.phase=transport?'transport':checking?'check':source?'source':'setup';try{const v=fn(...args);f.outcome=checking?(v?'checked':'rejected'):source?(v&&(v.tree||v.leaf||v.split||v.kind==='refuted')?'proof':'failed'):'done';return v}finally{this.end(f)}}
 audit(){
  if(this.stack.length)throw Error('unclosed ledger');const started=now(),state=Object.keys(this.machine.state),results:any[]=[]
  const ancestor=(f:Frame,kind:string):Frame|undefined=>{let p:Frame|undefined=f;while(p){if(p.kind===kind)return p;p=p.parent===undefined?undefined:this.frames[p.parent]}return undefined}
  const helperFrames=this.frames.filter(f=>f.kind==='helper'),attempts=this.frames.filter(f=>f.kind==='attempt')
  const costs=(a:Frame)=>{const out={setup:0,failed:0,source:0,check:0,transport:0};for(const f of this.frames)if(ancestor(f,'attempt')===a){const phase=f.kind==='operation'?(f.phase==='source'?(f.outcome==='proof'?'source':'failed'):f.phase!):'setup';out[phase as keyof typeof out]+=f.exclusive??0}return out}
  for(const a of attempts){const h=a.meta.helper===undefined?undefined:this.frames[a.meta.helper],reads=h?.meta.cert.reads??[],norm=(x:any)=>normalize(x,reads,columnTerm),statement=norm(a.meta.good),literal=dependence(statement,state),data=a.data,cost=costs(a);let sourceChecked=false,targetChecked=false,rootChecked=false,used:any=null,rootProof:any=null,error:string|undefined
   const auditStart=now(),auditWallStart=performance.now();try{
    if(data?.sourceTree&&data.source){sourceChecked=checkConditionalProof(data.source,data.sourceTree,data.sourcePath);if(sourceChecked){const dep=dependencies(data.source,data.sourceTree,data.sourcePath,t=>this.marks.get(t));used={indices:dep.indices,premises:dep.indices.map(i=>norm(data.source.hyps[i])),path:dep.atoms.map(atom=>({holds:atom.holds,condition:norm({op:'<=',a:linearExpr(atom.lin),b:{op:'const',value:0}})}))}}}
    if(data?.tree&&data.target)targetChecked=checkConditionalProof(data.target,data.tree,data.targetPath)
    const root=this.roots[0],source=data?.admitted?{...data.g,hyps:(data.lemma.slice??data.g.hyps.map((_:any,i:number)=>i)).map((i:number)=>data.g.hyps[i])}:data?.source,tree=data?.admitted?data.lemma.tree:data?.sourceTree,path=data?.admitted?proofPath(data.lemma.when,data.lemma.cut):data?.sourcePath
    if(root&&source&&tree&&(sourceChecked||data.admitted)&&data?.tree&&independent(literal)){
     const terms=['<=','<'].includes(a.meta.good.op)?a.meta.good:undefined
     // Only exact unguarded root transport; no solver and no borrowed cuts.
     if(terms){const left=linear(terms.a,path),right=linear(terms.b,path);if(left&&right){const cut=sub(left,right);if(terms.op==='<')cut['1']=(cut['1']??0)+1;const begin=now(),lemma=admitConditionalCut(root,source,tree,path,new Map(),cut,[],Infinity);if(lemma&&!lemma.when.length){const small={...root,hyps:(lemma.slice??root.hyps.map((_:any,i:number)=>i)).map((i:number)=>root.hyps[i]!)};rootChecked=check(small,lemma.tree,proofPath([],lemma.cut));rootProof={lemma,goal:small,cost:now()-begin,dependence:dependence(norm(small.hyps),state)}}}}
    }
   }catch(e){error=String(e)}
   const dep=used?dependence([used.premises,used.path],state):null,eligible=targetChecked&&rootChecked&&independent(rootProof.dependence)
   results.push({id:a.id,helper:h?.name,phase:h?.meta.phase,entryPath:h?.meta.path?[...h.meta.path]:[],kind:a.name,statement,key:JSON.stringify(statement),literal,proofDependence:dep,sourceChecked,targetChecked,emitted:!!data?.tree,admitted:!!data?.admitted,productionChecked:data?.productionChecked??false,eligible,rootChecked,rootDependence:rootProof?.dependence,rootAdmissionUnits:rootProof?.cost??0,units:cost,totalExclusive:Object.values(cost).reduce((x,y)=>x+y,0),auditUnits:now()-auditStart,auditWallMs:performance.now()-auditWallStart,premises:used,sourceMarks:this.snapshots(data?.sourceTree),targetMarks:this.snapshots(data?.tree),error,source:data?.source,sourceTree:data?.sourceTree,sourcePath:data?.sourcePath?[...data.sourcePath]:null,target:data?.target,tree:data?.tree,targetPath:data?.targetPath?[...data.targetPath]:null,rootProof,reads})
  }
  const helperRootUnits=helperFrames.filter(f=>{let p=f.parent;while(p!==undefined){if(this.frames[p]!.kind==='helper')return false;p=this.frames[p]!.parent}return true}).reduce((n,f)=>n+(f.units??0),0),attemptUnits=results.reduce((n,r)=>n+r.totalExclusive,0)
  return {law:this.law,op:this.op,results,helperRootUnits,attemptUnits,nonAttemptHelperUnits:helperRootUnits-attemptUnits,auditUnits:now()-started,frames:this.frames.map(({meta,data:_data,...f})=>({...f,meta:f.kind==='helper'?{goal:meta.goal.name,hyps:meta.goal.hyps.length,reads:meta.cert.reads.length}:f.kind==='attempt'?{helper:meta.helper}:undefined}))}
 }
}
function linearExpr(lin:Record<string,number>):any{const xs:any[]=Object.entries(lin).map(([k,v])=>k==='1'?{op:'const',value:v}:{op:'mul',k:v,a:{op:'var',name:k}});return xs.reduce((a,b)=>({op:'add',a,b}),{op:'const',value:0})}
export const lemmaRecorder=new Recorder()
