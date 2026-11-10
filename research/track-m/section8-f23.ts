// Research-only F2/F3. All caches are proposer hints over immutable objects;
// the final, unchanged checkMC must still check every returned certificate.
import {type Goal,type LemmaCut,type Path,type Tree,canon,check} from '../../kernel/kernel.ts'
import {rowsAt} from '../../kernel/prove.ts'
export const f23Stats={sliced:0,sliceHits:0,fullHyps:0,sliceHyps:0,independentHits:0,retargetHits:0}
const pathKey=(path:Path)=>JSON.stringify([...path].map(([key,a])=>[key,a.holds,canon(a.lin)]))
const leaves=new WeakMap<Goal,WeakMap<Tree,Map<string,boolean>>>()
export function slicedCheck(goal:Goal,tree:Tree,path:Path):boolean{
 if(!('leaf'in tree))return check(goal,tree,path)
 let trees=leaves.get(goal);if(!trees)leaves.set(goal,trees=new WeakMap())
 let paths=trees.get(tree);if(!paths)trees.set(tree,paths=new Map())
 const key=pathKey(path),old=paths.get(key);if(old!==undefined){f23Stats.sliceHits++;return old}
 f23Stats.sliced++;f23Stats.fullHyps+=goal.hyps.length
 let ok=false
 try{
  const rows=rowsAt(goal,path),needed=new Set<number>(),visited=new Set<number>(),sq=tree.squares?.length??0
  const mark=(i:number):void=>{if(visited.has(i))return;visited.add(i);if(!Number.isSafeInteger(i)||i<0)throw new Error('invalid input');if(i<rows.length){const src=rows[i]!.src;if(src&&'fact'in src)needed.add(src.fact)}else if(i>=rows.length+sq){const p=tree.products?.[i-rows.length-sq];if(!p)throw new Error('invalid product');mark(p[0]);mark(p[1])}}
  for(const step of tree.leaf)if(step.kind==='input')mark(step.index)
  // Retain even unused products: they are part of the literal certificate.
  for(const [a,b]of tree.products??[]){mark(a);mark(b)}
  const small={...goal,hyps:[...needed].sort((a,b)=>a-b).map(i=>goal.hyps[i]!)},target=rowsAt(small,path),at=new Map<string,number>()
  f23Stats.sliceHyps+=small.hyps.length
  target.forEach((row,i)=>{const id=canon(row.lin);if(!at.has(id))at.set(id,i)})
  const index=(i:number):number=>{if(i>=rows.length)return i-rows.length+target.length;const moved=at.get(canon(rows[i]!.lin));if(moved===undefined)throw new Error('missing row');return moved}
  const moved:Tree={...tree,leaf:tree.leaf.map(s=>s.kind==='input'?{...s,index:index(s.index)}:s),...(tree.products?{products:tree.products.map(([a,b])=>[index(a),index(b)] as [number,number])}:{})}
  ok=check(small,moved,path)
 }catch{ok=false}
 if(paths.size>=4096)paths.clear();paths.set(key,ok);return ok
}
const independent=new WeakMap<Goal,WeakSet<LemmaCut>>()
export function memoIndependent(goal:Goal,lemma:LemmaCut,compute:()=>boolean):boolean{
 let set=independent.get(goal);if(!set)independent.set(goal,set=new WeakSet())
 if(set.has(lemma)){f23Stats.independentHits++;return true}
 const ok=compute();if(ok)set.add(lemma);return ok
}
const retargets=new WeakMap<Goal,WeakMap<Goal,WeakMap<LemmaCut,Map<string,LemmaCut>>>>()
export function memoRetarget(from:Goal,to:Goal,lemma:LemmaCut,scope:Path,onlyMissing:boolean,compute:()=>LemmaCut|undefined):LemmaCut|undefined{
 let goals=retargets.get(from);if(!goals)retargets.set(from,goals=new WeakMap())
 let cuts=goals.get(to);if(!cuts)goals.set(to,cuts=new WeakMap())
 let paths=cuts.get(lemma);if(!paths)cuts.set(lemma,paths=new Map())
 const key=String(onlyMissing)+pathKey(scope),old=paths.get(key);if(old){f23Stats.retargetHits++;return old}
 const result=compute();if(result){if(paths.size>=4096)paths.clear();paths.set(key,result)}return result
}
const indices=new WeakMap<Goal,Map<string,number>>()
export function targetIndex(goal:Goal):Map<string,number>{let at=indices.get(goal);if(!at){at=new Map();for(const [i,h]of goal.hyps.entries()){const k=JSON.stringify(h);if(!at.has(k))at.set(k,i)}indices.set(goal,at)}return at}
