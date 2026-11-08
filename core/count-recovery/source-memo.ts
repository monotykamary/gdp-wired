// Reuse untrusted completed subproofs across retries of one source obligation.
// A changed source or path order always goes through the existing transport.
import {type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {clock,widen,withDeadline} from '../../kernel/prove.ts'
export type SourceProofMemo={get:(goal:Goal,path:Path,until:number)=>Tree|undefined,put:(goal:Goal,path:Path,tree:Tree)=>void}
export function sourceProofMemo():SourceProofMemo{
 const entries=new Map<string,{goal:Goal,path:Path,tree:Tree}>()
 const key=(path:Path)=>JSON.stringify([...path].map(([id,p])=>[id,p.holds]).sort(([a],[b])=>String(a).localeCompare(String(b))))
 return {
  get(goal,path,until){
   if(clock()>=until)return undefined
   const old=entries.get(key(path));if(!old)return undefined
   return withDeadline(until,()=>widen(old.goal,goal,old.tree,{},old.path,path))
  },
  put(goal,path,tree){entries.set(key(path),{goal,path:new Map(path),tree})},
 }
}
