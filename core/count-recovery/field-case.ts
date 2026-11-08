// A count-free live conclusion should not pay for unrelated count instances.
// Every projection is weakening-only, and every tree is transported to g.
import {type C,type Machine} from '../machine.ts'
import {type CountCert,type Goal,type Path,type Tree} from '../../kernel/kernel.ts'
import {clock,grow,widen,withDeadline} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {fieldOnlyGoal} from './field-only.ts'
import {foldPath} from './fold-path.ts'
export function fieldCase(m:Machine,g:Goal,cert:Pick<CountCert,'reads'|'insts'>,claim:C|undefined,path:Path,until:number,trace?:(e:Record<string,unknown>)=>void):Tree|undefined{
 const field=fieldOnlyGoal(g,m,cert,claim,path)
 if(!field||clock()>=until)return undefined
 const began=clock(),folded=foldPath(field,path),query=modelSequence(path)(folded.goal,until)
 const reduced=!('tree'in query)&&query.why===REFUTED&&query.core?.length?{...folded.goal,hyps:query.core.map(i=>folded.goal.hyps[i]!)}:folded.goal
 const out='tree'in query?query:grow(reduced,path,{nodes:0,until,units:true})
 const expanded='tree'in out?withDeadline(until,()=>widen(reduced,folded.goal,out.tree,{},path,path)):undefined
 const lifted=expanded&&withDeadline(until,()=>widen(folded.goal,field,expanded,folded.opaque,path,path))
 const tree=lifted&&withDeadline(until,()=>widen(field,g,lifted,{},path,path))
 trace?.({stage:'field-case',hyps:field.hyps.length,core:query.core?.length,ms:Math.round(clock()-began),proposed:!!tree,outcome:'tree'in query?'tree':query.stuck,...(!('tree'in query)&&query.stuck==='sat'?{model:query.witness}:{})})
 return tree
}
