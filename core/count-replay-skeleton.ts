// An untrusted proof supplies split hints only. Every replacement leaf is
// proved from the original goal/path by the ordinary linear solver/checker.
import {type Goal,type Path,type Tree,canon,check} from '../kernel/kernel.ts'
import {late,rowsAt} from '../kernel/prove.ts'
import {solve} from './solver.ts'
export function replayLinearSkeleton(goal:Goal,hint:Tree,root:Path,until:number,options:{deferCheck?:boolean}={}):Tree|undefined{
 const go=(tree:Tree,path:Path):Tree|undefined=>{
  if(late(until))return
  if('leaf'in tree){const result=solve(rowsAt(goal,path),2000);if(result.kind!=='refuted')return;const out:Tree={leaf:result.steps};return options.deferCheck||check(goal,out,path)?out:undefined}
  const id=canon(tree.split),known=path.get(id)?.holds
  if(known!==undefined)return go(known?tree.yes:tree.no,path)
  const yes=go(tree.yes,new Map(path).set(id,{lin:tree.split,holds:true}));if(!yes)return
  const no=go(tree.no,new Map(path).set(id,{lin:tree.split,holds:false}));return no?{split:tree.split,yes,no}:undefined
 }
 const tree=go(hint,root);return tree&&(options.deferCheck||check(goal,tree,root))?tree:undefined
}
