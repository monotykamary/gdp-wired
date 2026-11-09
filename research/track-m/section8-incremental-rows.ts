// Research F4: cache hypothesis facts by the exact decisions they read.
// The default builder is unchanged; the disposable installer supplies an exact
// copy of its row assembler as untrusted code, with cached facts as input.
import type {C} from '../../core/machine.ts'
import {type Lin} from '../../core/solver.ts'
import {type Goal,type Path,type Seen,canon,facts,leafConstraintsReusing,reusing} from '../../kernel/kernel.ts'
type Block={rows:Lin[],keys:string[]}
type Entry={blocks:Block[],deps:Map<string,Set<number>>}
const cache=new WeakMap<Goal,Map<string,Entry>>()
export const incrementalStats={roots:0,children:0,hypotheses:0,recomputed:0,reused:0,clears:0}
const buildRows=(goal:Goal,path:Path,_factsOf:(h:C)=>Lin[])=>leafConstraintsReusing(goal,path)
function evaluate(h:C,path:Path):Block{
 const seen:Seen<Lin[]>={},rows=reusing(seen,path,p=>facts(h,p)),root=seen.root
 if(!root||!('reads'in root))throw new Error('expected fresh decision trace')
 incrementalStats.recomputed++;return {rows,keys:root.reads.map(([key])=>key)}
}
function rootEntry(goal:Goal):Entry{
 incrementalStats.roots++;const blocks=goal.hyps.map(h=>evaluate(h,new Map())),deps=new Map<string,Set<number>>()
 blocks.forEach((b,i)=>b.keys.forEach(k=>{let set=deps.get(k);if(!set)deps.set(k,set=new Set());set.add(i)}))
 return {blocks,deps}
}
function child(goal:Goal,parent:Entry,path:Path,key:string):Entry{
 const affected=parent.deps.get(key),blocks=parent.blocks.slice(),deps=new Map(parent.deps),copied=new Set<string>()
 incrementalStats.children++;incrementalStats.hypotheses+=blocks.length;incrementalStats.reused+=blocks.length-(affected?.size??0)
 const writable=(k:string):Set<number>=>{let set=deps.get(k);if(!copied.has(k)){deps.set(k,set=new Set(set));copied.add(k)}return set!}
 for(const i of affected??[]){const old=blocks[i]!,next=evaluate(goal.hyps[i]!,path);for(const k of old.keys)writable(k).delete(i);for(const k of next.keys)writable(k).add(i);blocks[i]=next}
 return {blocks,deps}
}
export function incrementalRows(goal:Goal,path:Path):ReturnType<typeof leafConstraintsReusing>{
 let entries=cache.get(goal);if(!entries)cache.set(goal,entries=new Map())
 const cap=Math.min(4096,Math.max(1,Math.floor(250000/Math.max(1,goal.hyps.length))))
 if(entries.size>=cap){entries.clear();incrementalStats.clears++}
 let current=entries.get('');if(!current){current=rootEntry(goal);entries.set('',current)}
 let id='';const prefix:Path=new Map()
 for(const [key,atom]of path){prefix.set(key,atom);id+=JSON.stringify([key,atom.holds,canon(atom.lin)])+'|';let next=entries.get(id);if(!next){next=child(goal,current,prefix,key);if(entries.size<cap)entries.set(id,next)}current=next}
 let i=0;const final=current;return buildRows(goal,path,()=>final.blocks[i++]!.rows)
}
