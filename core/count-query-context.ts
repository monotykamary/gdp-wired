// Untrusted copy-query projection. Keep count premises and the target intact;
// remove only other witnesses and specialize conditionals on the actual root.
// Every returned proof must still be reindexed and checked on the full goal.
import {type C} from './machine.ts'
import {type Count,type CountInst,type Path} from '../kernel/kernel.ts'
import {projectCountFree} from './count-project-free.ts'
import {projectCountWitness} from './count-project-witness.ts'
export function copyQueryContext(hyps:C[],path:Path,counts:Count[],all:CountInst[],selected:CountInst[]):C[]{
 const witnesses=new Set(selected.map(inst=>inst.wit)),other=new Set(all.filter(inst=>!witnesses.has(inst.wit)).map(inst=>inst.wit))
 const common=projectCountFree(hyps,path,new Set(),other,true)
 return selected.length?projectCountWitness(common,counts,selected):common
}
