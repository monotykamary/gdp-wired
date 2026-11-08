// Untrusted, immutable structural sharing for the existing row builder. No
// duplicated arithmetic semantics: the unchanged leafConstraintsReusing builds
// every miss; the kernel still checks against original, uncanonicalized goals.
import type {C} from '../core/machine.ts'
import {type Constraint} from '../core/solver.ts'
import {type Goal,type Path,canon,leafConstraintsReusing} from './kernel.ts'
const originals=new WeakMap<object,object>(),ids=new WeakMap<object,number>()
const nodes=new Map<string,object>()
let serial=0,keyChars=0
export const rowReuseStats={nodeHits:0,nodeMisses:0,goalHits:0,rowsHits:0,rowsBuilt:0}
const id=(o:object):number=>{let n=ids.get(o);if(n===undefined)ids.set(o,(n=++serial));return n}
function intern(value:unknown):unknown{
 if(!value||typeof value!=='object')return value
 const had=originals.get(value)
 if(had)return had
 const values=Array.isArray(value)?value.map(intern):Object.fromEntries(Object.entries(value).map(([k,v])=>[k,intern(v)]))
 const ref=(v:unknown):unknown=>v&&typeof v==='object'?['@',id(v)]:typeof v==='number'&&!Number.isFinite(v)?['number',String(v)]:['value',v]
 const key=Array.isArray(values)?JSON.stringify(['array',values.map(ref)]):JSON.stringify(['object',Object.entries(values).sort(([a],[b])=>a.localeCompare(b)).map(([k,v])=>[k,ref(v)])])
 let out=nodes.get(key)
 if(out)rowReuseStats.nodeHits++
 else{
  if(nodes.size>=100000||keyChars+key.length>32*1024*1024){nodes.clear();keyChars=0}
  nodes.set(key,(out=values));keyChars+=key.length;rowReuseStats.nodeMisses++
 }
 originals.set(value,out);originals.set(out,out);id(out)
 return out
}
const goals=new WeakMap<Goal,Goal>(),goalPool=new Map<string,Goal>()
function sharedGoal(goal:Goal):Goal{
 let out=goals.get(goal)
 if(out)return out
 const hyps=goal.hyps.map(c=>intern(c) as C),key=hyps.map(id).join(',')
 out=goalPool.get(key)
 if(out){rowReuseStats.goalHits++;goalPool.delete(key)}
 else out={name:goal.name,hyps}
 if(goalPool.size>=128)goalPool.delete(goalPool.keys().next().value!)
 goalPool.set(key,out);goals.set(goal,out)
 return out
}
const rows=new Map<string,Constraint[]>()
export function proverRows(goal:Goal,path:Path):Constraint[]{
 const shared=sharedGoal(goal)
 // Path ordering matters for input-row indices. Include the actual atom as
 // well as its lookup key, so even malformed key/atom pairs cannot alias.
 const key=JSON.stringify([id(shared),[...path].map(([key,a])=>[key,a.holds,canon(a.lin)])])
 let out=rows.get(key)
 if(out){rowReuseStats.rowsHits++;rows.delete(key);rows.set(key,out);return out}
 rowReuseStats.rowsBuilt++
 out=leafConstraintsReusing(shared,path)
 if(rows.size>=8192)rows.delete(rows.keys().next().value!)
 rows.set(key,out);return out
}
