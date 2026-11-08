// Reuse untrusted completed subproofs across retries of one source obligation.
// A changed source or path order always goes through the existing transport.
import {type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {renameProof} from './rename-proof.ts'
import {clock,widen,withDeadline} from '../../kernel/prove.ts'
export type SourceProofMemo={get:(goal:Goal,path:Path,until:number)=>Tree|undefined,put:(goal:Goal,path:Path,tree:Tree)=>void}
export function sourceProofMemo():SourceProofMemo{
 const entries=new Map<string,{goal:Goal,path:Path,tree:Tree}>()
 const key=(path:Path)=>JSON.stringify([...path].map(([id,p])=>[id,p.holds]).sort(([a],[b])=>String(a).localeCompare(String(b))))
 return {
  get(goal,path,until){
   if(clock()>=until)return undefined
   const old=entries.get(key(path));if(old)return withDeadline(until,()=>widen(old.goal,goal,old.tree,{},old.path,path))
   // A different activation path may leave every used source row unchanged.
   // Match those rows exactly; never search for or assume a symmetry here.
   const distance=(p:Path)=>{let n=0;for(const [id,v]of path)if(p.get(id)?.holds!==v.holds)n++;for(const id of p.keys())if(!path.has(id))n++;return n}
   const nearby=[...entries.values()].filter(e=>e.goal===goal).sort((a,b)=>distance(a.path)-distance(b.path)).slice(0,8)
   for(const e of nearby){const tree=renameProof(e.goal,e.tree,e.path,path,{},Math.min(until,clock()+25),goal);if(tree)return tree}
   return undefined
  },
  put(goal,path,tree){entries.set(key(path),{goal,path:new Map(path),tree})},
 }
}
