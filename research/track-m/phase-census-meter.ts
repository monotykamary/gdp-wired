// Diagnostic only; installed hooks retain references and defer proof-use audits.
export type Phase='other'|'demand'|'proposals'|'A'|'B'|'C'|'kernel'|'search'
type Frame={phase:Phase,effective:Phase,site:string,start:number}
type Closure={id:string,goal:string,cuts:any[],rounds:any[],segments:any[],phase?:string,phaseAt?:number}
type Leaf={id:string,closure:string,path:any,available:any[],numeric?:any,proof?:any,query?:any,transported?:boolean}
export class PhaseCensus {
 enabled=false
 onSlice?: (phase:Phase,ms:number)=>void
 readonly totals:Record<Phase,number>={other:0,demand:0,proposals:0,A:0,B:0,C:0,kernel:0,search:0}
 readonly sites=new Map<string,{calls:number,inclusiveMs:number}>()
 readonly closures:Closure[]=[]
 readonly leaves:Leaf[]=[]
 private stack:Frame[]=[]
 private contexts:Closure[]=[]
 private ids=new WeakMap<object,string>()
 private last=0
 private serial=0
 private rounds=new Map<Closure,{start:number,exclusive:number}>()
 constructor(private now=()=>performance.now()){}
 private tick(){const now=this.now(),top=this.stack.at(-1);if(top){const ms=now-this.last;this.totals[top.effective]+=ms;this.onSlice?.(top.effective,ms)}this.last=now;return now}
 private effective(phase:Phase):Phase{const parent=this.stack.at(-1)?.effective;if(parent==='kernel'||phase==='kernel')return 'kernel';return phase==='search'&&parent&&['A','B','C'].includes(parent)?parent:phase}
 private enter(phase:Phase,site:string){const now=this.tick();this.stack.push({phase,effective:this.effective(phase),site,start:now})}
 private leave(){const now=this.tick(),frame=this.stack.pop();if(frame){const stat=this.sites.get(frame.site)??{calls:0,inclusiveMs:0};stat.calls++;stat.inclusiveMs+=now-frame.start;this.sites.set(frame.site,stat)}}
 run<T>(phase:Phase,site:string,f:()=>T):T{if(!this.enabled)return f();this.enter(phase,site);try{return f()}finally{this.leave()}}
 reset(){if(this.stack.length)throw new Error('census scope still open');for(const k of Object.keys(this.totals) as Phase[])this.totals[k]=0;this.sites.clear();this.closures.length=0;this.leaves.length=0;this.contexts.length=0;this.ids=new WeakMap();this.serial=0;this.rounds.clear();this.last=this.now()}
 closure<T>(goal:any,_cert:any,_root:any,f:()=>T):T{
  if(!this.enabled)return f()
  const context:Closure={id:`closure-${++this.serial}`,goal:goal.name,cuts:[],rounds:[],segments:[]}
  this.closures.push(context);this.contexts.push(context);this.enter('other','deriveCountClosure')
  const depth=this.stack.length
  try{return f()}finally{this.closeSegment(context);while(this.stack.length>=depth)this.leave();this.contexts.pop();this.rounds.delete(context)}
 }
 private closeSegment(c:Closure){if(c.phase!==undefined)c.segments.push({phase:c.phase,wallMs:this.now()-c.phaseAt!});c.phase=undefined}
 phase(phase:'A'|'B'|'other'){
  if(!this.enabled)return
  const c=this.contexts.at(-1);if(!c)return
  this.closeSegment(c);const now=this.tick();c.phase=phase;c.phaseAt=now
  const frame=this.stack.at(-1);if(frame){frame.phase=phase;frame.effective=this.effective(phase)}
 }
 cut(saved:any,_goal:any,cert:any){if(!this.enabled)return;const c=this.contexts.at(-1);if(!c)return;const id=`${c.id}/cut-${c.cuts.length+1}`;this.ids.set(saved,id);c.cuts.push({id,phase:c.phase,index:saved.index??null,when:saved.lemma.when,cut:saved.lemma.cut,...(saved.index===undefined?{}:{instance:cert.insts[saved.index]})})}
 beginRound(){if(!this.enabled)return;const c=this.contexts.at(-1);if(c){this.tick();this.rounds.set(c,{start:this.now(),exclusive:this.totals.B})}}
 endRound(summary:any){if(!this.enabled)return;const c=this.contexts.at(-1),round=c&&this.rounds.get(c);if(!c||!round)return;this.tick();c.rounds.push({...summary,wallMs:this.now()-round.start,exclusiveMs:this.totals.B-round.exclusive});this.rounds.delete(c)}
 beginLeaf(path:any,available:any[]):Leaf|undefined{if(!this.enabled)return;const c=this.contexts.at(-1);if(!c)return;const leaf:Leaf={id:`${c.id}/leaf-${this.leaves.filter(l=>l.closure===c.id).length+1}`,closure:c.id,path,available:available.slice()};this.leaves.push(leaf);this.enter('C','closure leaf query');return leaf}
 endLeaf(leaf:Leaf|undefined,numeric:any,proof:any,query:any){if(!leaf)return;leaf.numeric=numeric;leaf.proof=proof;leaf.query=query;this.leave()}
 finishLeaf(leaf:Leaf|undefined,transported:boolean){if(leaf)leaf.transported=transported}
 audit(check:(g:any,t:any,p:any)=>boolean,used:(g:any,t:any,p:any)=>Set<number>){
  if(this.stack.length)throw new Error('audit attempted inside measured search')
  const start=this.now(),proofIds=new Set<string>(),coreIds=new Set<string>(),offeredIds=new Set<string>(),raw:any[]=[]
  const leaves=this.leaves.map(leaf=>{
   const offered=leaf.available.flatMap(s=>{const id=this.ids.get(s),at=leaf.numeric?.hyps.indexOf(s.good)??-1;return id&&at>=0?[{id,at}]:[]})
   offered.forEach(s=>offeredIds.add(s.id))
   let checked=false,refs=new Set<number>(),error:string|undefined
   if(leaf.proof)try{checked=check(leaf.numeric,leaf.proof,leaf.path);if(checked)refs=used(leaf.numeric,leaf.proof,leaf.path)}catch(e){error=String(e)}
   const cited=offered.filter(s=>refs.has(s.at)).map(s=>s.id),core=offered.filter(s=>leaf.query?.core?.includes(s.at)).map(s=>s.id)
   cited.forEach(id=>proofIds.add(id));core.forEach(id=>coreIds.add(id))
   if(leaf.proof)raw.push({id:leaf.id,numeric:leaf.numeric,path:[...leaf.path],proof:leaf.proof,offered,cited,checked})
   return {id:leaf.id,closure:leaf.closure,outcome:leaf.proof?'proposed-proof':leaf.query?.stuck??'unknown',transported:leaf.transported??false,checked,offered:offered.map(s=>s.id),proofReferenced:cited,coreReferenced:core,...(error?{error}:{}),path:[...leaf.path]}
  })
  const proven=this.closures.flatMap(c=>c.cuts.map(cut=>cut.id)),usedIds=new Set([...proofIds,...coreIds])
  return {wallMs:this.now()-start,closures:this.closures,leaves,counts:{proven:proven.length,offered:offeredIds.size,proofReferenced:proofIds.size,coreReferenced:coreIds.size,referenced:usedIds.size,neverOffered:proven.filter(id=>!offeredIds.has(id)).length,offeredNotReferenced:[...offeredIds].filter(id=>!usedIds.has(id)).length},ids:{proven,offered:[...offeredIds],proofReferenced:[...proofIds],coreReferenced:[...coreIds],referenced:[...usedIds]},raw}
 }
 capture(){if(this.stack.length)throw new Error('capture attempted inside measured search');const holder=new PhaseCensus(this.now);holder.ids=this.ids;holder.closures.push(...this.closures);holder.leaves.push(...this.leaves);return holder}
 snapshot(){this.tick();return {exclusiveMs:{...this.totals},sites:Object.fromEntries(this.sites)}}
}
export const census=new PhaseCensus()
census.enabled=process.env.TRACK_M_PHASE_CENSUS==='1'
