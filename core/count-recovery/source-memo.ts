// Reuse untrusted completed subproofs. A shared machine scope retains separate
// goal/path entries; every cross-context candidate must transport all used rows.
import {type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {renameProof} from './rename-proof.ts'
import {clock,widen,withDeadline} from '../../kernel/prove.ts'
import {env} from '../solver.ts'
export type SourceProofMemo={get:(goal:Goal,path:Path,until:number)=>Tree|undefined,put:(goal:Goal,path:Path,tree:Tree)=>void}
type Entry={goal:Goal,path:Path,tree:Tree,context?:string}
type Cache={entries:Map<string,Entry>,ids:WeakMap<Goal,number>,next:number,indices:WeakMap<object,Map<string,number>>}
const scopes=new WeakMap<object,Cache>(),fresh=():Cache=>({entries:new Map(),ids:new WeakMap(),next:0,indices:new WeakMap()})
export const sourceMemoStats={foreignAttempts:0,foreignHits:0,crossLawHits:0,localHits:0}
export function sourceProofMemo(scope?:object,context?:string):SourceProofMemo{
 const shared=env.GDP_SOURCE_CONTEXTS!=='0'
 let cache=shared&&scope?scopes.get(scope):undefined
 if(!cache){cache=fresh();if(shared&&scope)scopes.set(scope,cache)}
 const {entries,ids}=cache,data=cache
 const key=(goal:Goal,path:Path)=>{
  let id=ids.get(goal);if(id===undefined){id=data.next++;ids.set(goal,id)}
  return (shared?`${id}/`:'')+JSON.stringify([...path].map(([atom,p])=>[atom,p.holds]).sort(([a],[b])=>String(a).localeCompare(String(b))))
 }
 return {
  get(goal,path,until){
   if(clock()>=until)return undefined
   const old=entries.get(key(goal,path));if(old){const tree=withDeadline(until,()=>widen(old.goal,goal,old.tree,{},old.path,path));if(tree){sourceMemoStats.localHits++;return tree}if(!shared)return undefined}
   const distance=(p:Path)=>{let n=0;for(const [id,v]of path)if(p.get(id)?.holds!==v.holds)n++;for(const id of p.keys())if(!path.has(id))n++;return n}
   const nearby=[...entries.values()].filter(e=>shared||e.goal===goal).sort((a,b)=>Number(b.goal===goal)-Number(a.goal===goal)||distance(a.path)-distance(b.path)).slice(0,8)
   const foreignEnd=Math.min(until,clock()+50)
   for(const e of nearby){
    const foreign=e.goal!==goal;if(foreign&&clock()>=foreignEnd)break
    if(foreign)sourceMemoStats.foreignAttempts++
    const tree=renameProof(e.goal,e.tree,e.path,path,{},Math.min(until,clock()+(foreign?10:25)),goal,shared&&env.GDP_SOURCE_INDEX!=='0'?data.indices:undefined)
    if(tree){if(foreign){sourceMemoStats.foreignHits++;if(e.context!==context)sourceMemoStats.crossLawHits++}else sourceMemoStats.localHits++;return tree}
   }
   return undefined
  },
  put(goal,path,tree){const id=key(goal,path);entries.delete(id);entries.set(id,{goal,path:new Map(path),tree,context});if(shared&&entries.size>128)entries.delete(entries.keys().next().value!)},
 }
}
