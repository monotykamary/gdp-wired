// Untrusted closure of arithmetic read-key guards. All added facts carry a
// refutation of their opposite branch; the caller checks the combined tree.
import {type C,type E,walkOnce} from '../../core/machine.ts'
import {type Goal,type Path,type Tree,canon,facts,truth} from '../../kernel/kernel.ts'
import {refuteFast,scale} from '../../core/solver.ts'
import {clock,rowsAt} from '../../kernel/prove.ts'
export function closeKeyReads(g:Goal,root:Path,reads:{map:string,key:E}[],wits:Set<string>,until:number):{path:Path,cuts:{split:Record<string,number>,no:Tree}[]}{
 const proposals:C[]=[],seen=new Set<string>(),cuts:{split:Record<string,number>,no:Tree}[]=[],cells=new Map<string,E[]>();let path=root
 const add=(c:C)=>{const id=JSON.stringify(c);if(!seen.has(id)){seen.add(id);proposals.push(c)}}
 const member=(key:E)=>{let hit=false;walkOnce(key,(o:any)=>{if(o.op==='var'&&wits.has(o.name))hit=true});return hit}
 for(const {map,key}of reads){
  const xs=cells.get(map)??[];if(!xs.some(k=>JSON.stringify(k)===JSON.stringify(key)))xs.push(key);cells.set(map,xs)
  if(!member(key))continue
  const subs:{a:E,b:E}[]=[];walkOnce(key,(o:any)=>{if(o.op==='sub')subs.push(o)})
  for(const s of subs.reverse())add({op:'<=',a:s.b,b:s.a})
 }
 for(const keys of cells.values())for(let i=0;i<keys.length;i++)for(let j=i+1;j<keys.length;j++)if(member(keys[i]!)||member(keys[j]!))add({op:'=',a:keys[i]!,b:keys[j]!})
 const force=(split:Record<string,number>):boolean=>{
  const id=canon(split);if(path.get(id)?.holds===true)return true
  if(clock()>=until)return false
  const other=new Map(path).set(id,{lin:split,holds:false}),out=refuteFast(rowsAt(g,other),128)
  if(out?.kind!=='refuted')return false
  cuts.push({split,no:{leaf:out.steps}});path=new Map(path).set(id,{lin:split,holds:true});return true
 }
 for(const c of proposals.slice(0,24)){
  if(clock()>=until)break
  if(truth(c,path)!==undefined)continue
  for(const split of facts(c,path))if(!force(split)){const inverse=scale(split,-1);inverse['1']=(inverse['1']??0)+1;force(inverse)}
 }
 return {path,cuts}
}
