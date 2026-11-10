// Untrusted first split for a small count core: carried membership at the
// certificate's witness, before branching through large post-state terms.
import {n,type E} from '../../core/machine.ts'
import {type Goal,type Path,type Tree,canon,linear,truth} from '../../kernel/kernel.ts'
import {sub} from '../../core/solver.ts'
import {clock} from '../../kernel/prove.ts'
import {walkLive} from './live-dependencies.ts'
import {check,grow} from './wall-profile.ts'
export function carriedCase(g:Goal,root:Path,maps:readonly string[],wits:Set<string>,until:number,trace:object[]):Tree|undefined{
 let cell:E|undefined
 walkLive(g.hyps,root,(o:any)=>{if(!cell&&o.op==='get'&&maps.includes(o.map)&&o.key.op==='var'&&wits.has(o.key.name)&&truth({op:'<=',a:n(1),b:o},root)===undefined)cell=o})
 if(!cell)return undefined
 const value=linear(cell,root);if(!value)return undefined
 const split=sub({'1':1},value),id=canon(split),started=clock()
 const noPath=new Map(root).set(id,{lin:split,holds:false}),no=grow(g,noPath,{nodes:0,until,units:true})
 const yesPath=new Map(root).set(id,{lin:split,holds:true}),yes='tree'in no&&clock()<until?grow(g,yesPath,{nodes:0,until,units:true}):undefined
 const tree:Tree|undefined='tree'in no&&yes&&'tree'in yes?{split,yes:yes.tree,no:no.tree}:undefined,checked=!!tree&&check(g,tree,root)
 trace.push({stage:'carried-core',cell,ms:Math.round(clock()-started),no:'tree'in no,yes:!!yes&&'tree'in yes,checked})
 return checked?tree:undefined
}
