// Keep complete work/event ledgers, but only the first failed numeric snapshot
// per op/pass. Unlimited search must not retain every repeated large goal.
import {appendFileSync} from 'node:fs'
import {diagnostic as d} from './section10-diagnostic.ts'
import {realNow} from './without-deadlines.ts'
export function section12Recorder(journal:string){
 const capture=d.capture.bind(d),event=d.event.bind(d),end=d.end.bind(d),current=new Map<number,any>(),failures=new Map<string,any>()
 let last:any,start=realNow()
 const actionOf=(id:number|undefined)=>{let found:any;while(id!==undefined){const f=d.frames[id];if(!f)break;if(f.kind==='action'&&f.meta.selector==='op')found=f;id=f.parent}return found}
 const query=(q:any)=>q&&({stuck:q.stuck,why:q.why,core:q.core,witness:q.witness,tree:!!q.tree,nodes:q.nodes})
 d.capture=(data,source)=>{capture(data,source);last=d.captures.pop();if(last){Object.defineProperty(last,'source',{value:last.source,enumerable:false,configurable:true});last.query=query(last.query);last.available=last.available?.map(({index,good}:any)=>({index,good}));current.set(last.frame,last)}}
 d.model=(data)=>{if(last){last.model=data.model;last.violated=data.violated}d.event('model',{closure:data.closure,violated:data.violated})}
 d.event=(kind,data)=>{
  const small=kind==='numeric'?{capture:data.capture,closure:data.closure,round:data.round,query:query(data.query)}:kind==='source-query-result'?{index:data.index,query:query(data.query)}:kind==='source-result'?{index:data.index,outcome:data.outcome,accepted:data.accepted}:data
  // Source SAT points are not needed for the op ledger; failure snapshots keep
  // the relevant numeric model. Do not retain full source goals here.
  if(kind==='source-query-result'&&small.query)delete small.query.witness
  event(kind,small)
  const e=d.events.at(-1),action=actionOf(e?.frame)
  if(kind==='stop'||kind==='leaf-outcome'&&data.outcome!=='checked'){
   const key=JSON.stringify(action?.meta??{frame:e?.frame})
   if(!failures.has(key)){const c=current.get(e?.frame),copy=c?{...c}:null;if(copy&&c.source)Object.defineProperty(copy,'source',{value:c.source,enumerable:false});failures.set(key,{...e,action:action?.meta,capture:copy})}
  }
 }
 d.end=(f,result)=>{end(f,result);if(f.kind==='leaf'){current.delete(f.id);if(last?.frame===f.id)last=undefined}if(f.kind==='action'&&f.meta.selector==='op')appendFileSync(journal,JSON.stringify({event:'action-end',...f.meta,units:f.units,realWallMs:realNow()-start})+'\n')}
 return {
  latest(){return last},
  reset(label:string){d.reset(label);current.clear();failures.clear();last=undefined;start=realNow()},
  result(total:number){
   const leafParents=new Set(d.frames.filter(f=>f.kind==='leaf').map(f=>f.parent))
   const rootActions=d.frames.filter(f=>f.kind==='action'&&f.meta.selector==='op'&&actionOf(f.parent)===undefined),groups=new Map<string,any>()
   const key=(f:any)=>f.meta.value===null?'else':String(f.meta.value)
   const group=(f:any)=>{const op=key(f);let g=groups.get(op);if(!g){g={op,units:0,actionAttempts:0,leafVisits:0,leaves:0,cuts:0,sourceQueries:0,sat:0,refuted:0,unknown:0,reused:0,cacheChecked:0,cacheSat:0,cacheUnknown:0,rawRefuted:0};groups.set(op,g)}return g}
   for(const f of rootActions){const g=group(f);g.units+=f.units??0;g.actionAttempts++}
   for(const f of d.frames){const a=actionOf(f.id);if(!a)continue;const g=group(a);if(f.kind==='leaf'){g.leafVisits++;if(!leafParents.has(f.id))g.leaves++}if(f.kind==='source-query')g.sourceQueries++}
   for(const e of d.events){const a=actionOf(e.frame);if(!a)continue;const g=group(a);if(e.kind==='cut')g.cuts++;if(e.kind==='source-result'){const k=e.outcome==='checked'?'refuted':e.outcome==='sat'?'sat':e.outcome==='reused-model'?'reused':'unknown';g[k]++}if(e.kind==='source-cached')g[e.outcome==='checked'?'cacheChecked':e.outcome==='sat'?'cacheSat':'cacheUnknown']++;if(e.kind==='source-query-result'&&(e.query?.why==='refuted, not unfolded'||e.query?.tree))g.rawRefuted++}
   const final=d.events.findLast(e=>e.kind==='case-final-results'),target=final?.unresolved?.[0]
   const values=[...failures.values()],first=values.find(f=>target===undefined||f.action?.value===target||target==='else'&&f.action?.value===null)??values[0]??null
   return {ledger:[...groups.values()],outsideActions:total-rootActions.reduce((s,f)=>s+(f.units??0),0),firstFailure:first,finalUnresolved:final??null,trace:d.dump()}
  },
 }
}
