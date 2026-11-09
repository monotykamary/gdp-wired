// Untrusted arithmetic case proposals for natural subtraction in a source path.
// The ordinary kernel still checks all leaves and the combined tree.
import {type E,walkOnce} from '../machine.ts'
import {type Lin,sub} from '../solver.ts'
import {type Goal,type Path,type Tree,canon,columnTerm,linear,truth} from '../../kernel/kernel.ts'
import {clock} from '../../kernel/prove.ts'
import {check,grow} from './ops.ts'

export function naturalSplits(g:Goal,root:Path):Lin[]{
 const expressions:unknown[]=[g.hyps],seen=new Set<string>(),splits=new Map<string,Lin>()
 const columns=[...root.values()].flatMap(p=>Object.keys(p.lin))
 for(const name of columns){if(seen.has(name))continue;seen.add(name);const term=columnTerm(name);if(term){expressions.push(term);walkOnce(term,(o:any)=>{if(o.op==='var')columns.push(o.name)})}}
 walkOnce(expressions,(o:any)=>{
  if(o.op!=='sub'||truth({op:'<=',a:o.a as E,b:o.b as E},root)!==undefined)return
  const a=linear(o.a,root),b=linear(o.b,root);if(!a||!b)return
  const split=sub(a,b);splits.set(canon(split),split)
 })
 return [...splits.values()].slice(0,2)
}

export function proveNaturalCases(g:Goal,root:Path,until:number,trace:object[]=[],options:{deferCheck?:boolean}={}):Tree|undefined{
 const splits=naturalSplits(g,root);if(!splits.length)return undefined
 const started=clock()
 const go=(index:number,path:Path):Tree|undefined=>{
  if(clock()>=until)return undefined
  const split=splits[index]
  if(!split){
   const out=grow(g,path,{nodes:0,until:Math.min(until,clock()+100),units:false})
   trace.push({stage:'natural-case-leaf',proposed:'tree'in out,...(!('tree'in out)?{outcome:out.stuck,...('witness'in out?{model:out.witness}:{})}:{})})
   return 'tree'in out?out.tree:undefined
  }
  const id=canon(split);if(path.has(id))return go(index+1,path)
  const yes=go(index+1,new Map(path).set(id,{lin:split,holds:true}));if(!yes)return undefined
  const no=go(index+1,new Map(path).set(id,{lin:split,holds:false}))
  return no?{split,yes,no}:undefined
 }
 const tree=go(0,root),accepted=!!tree&&(options.deferCheck||check(g,tree,root))
 trace.push({stage:'natural-cases',cases:splits.length,ms:Math.round(clock()-started),checked:accepted&&!options.deferCheck,proposed:!!tree,deferred:!!options.deferCheck})
 return accepted?tree:undefined
}
