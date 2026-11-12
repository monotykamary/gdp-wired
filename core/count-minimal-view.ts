// Untrusted search policy. A smaller view is only a proposal: every returned
// tree is reindexed against the original goal. Checks are strict by default;
// explicit composition-only construction may defer them to its final checker.
import {type C} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {env,solve} from './solver.ts'
import {type CountDecl,type CountInst,type Goal,type MapRead,type Path,type Tree,check,mcGoal} from '../kernel/kernel.ts'
import {growCdcl} from '../kernel/cdcl.ts'
import {type Outcome,brokenOf,clock,fullRate,fullWork,rowsAt} from '../kernel/prove.ts'
import {projectCountFree} from './count-project-free.ts'
import {projectCountWitness,projectCountWitnessRoot} from './count-project-witness.ts'
import {rebasePath} from './count-rebase-path.ts'
import {replayLinearSkeleton} from './count-replay-skeleton.ts'
export function minimalTransportView(hyps:C[],decls:CountDecl[],reads:MapRead[],all:CountInst[],selected:CountInst[],path:Path):{goal:Goal,reads:MapRead[],path:Path}|undefined{
 if(!selected.length)return
 const counts=countsForReads(decls,reads);if(!counts)return
 const own=new Set(selected.map(inst=>inst.wit)),other=new Set(all.filter(inst=>!own.has(inst.wit)).map(inst=>inst.wit))
 const scalar=projectCountFree(hyps,path,new Set(decls.map(decl=>decl.map)),other,true)
 const premises=projectCountWitness(scalar,counts,selected),ids=new Set(selected.flatMap(inst=>inst.terms.map(([,id])=>id)))
 const minimal=reads.filter(([id])=>ids.has(id)),goal=mcGoal(premises,decls,{reads:minimal,insts:selected,picks:[]})
 return goal?{goal,reads:minimal,path:projectCountWitnessRoot(path,counts,selected)}:undefined
}
export type MinimalResult={kind:'proof'|'sat'|'unknown'|'rejected',minimalKind:'proof'|'sat'|'unknown'|'rejected',fallback:boolean,minimalUnits:number,fallbackUnits:number,tree?:Tree,witness?:Record<string,number>}
type Search=(goal:Goal,path:Path,budget:{nodes:number,until:number})=>Outcome
export function minimalViewFirst(full:Goal,minimal:Goal,path:Path,until:number,fallbackSearch:Search=growCdcl,minimalPath:Path=path,options:{deferCheck?:boolean,deferReplayCheck?:boolean}={}):MinimalResult{
 const began=fullWork(),units=()=> (fullWork()-began)/fullRate
 const search=(goal:Goal,solver:Search,root:Path):Outcome=>{
  if(clock()>=until)return {stuck:'unknown',path:root,why:'minimal-view deadline'}
  const direct=solve(rowsAt(goal,root),2000)
  return direct.kind==='refuted'?{tree:{leaf:direct.steps},nodes:0}:solver(goal,root,{nodes:0,until})
 }
 const small=search(minimal,growCdcl,minimalPath)
 if('tree'in small){
  // C2 ownership does not activate forwarding without its independent opt-in.
  const tree=minimal===full&&minimalPath===path?small.tree:(rebasePath(minimal,small.tree,minimalPath,path,until,full)??(env.GDP_COUNT_REPLAY_FORWARD==='1'
   ?replayLinearSkeleton(full,small.tree,path,until,{deferCheck:options.deferCheck===true&&options.deferReplayCheck===true})
   :replayLinearSkeleton(full,small.tree,path,until)))
  const checked=!!tree&&(options.deferCheck||check(full,tree,path))&&clock()<until
  return {kind:checked?'proof':'rejected',minimalKind:checked?'proof':'rejected',fallback:false,minimalUnits:units(),fallbackUnits:0,...(checked?{tree}:{})}
 }
 const minimalUnits=units()
 if(small.stuck!=='sat')return {kind:'unknown',minimalKind:'unknown',fallback:false,minimalUnits,fallbackUnits:0}
 if(small.witness&&brokenOf(minimal)(small.witness).length)throw Error('invalid minimal transport model')
 const result=search(full,fallbackSearch,path),checked='tree'in result&&(options.deferCheck||check(full,result.tree,path))&&clock()<until
 return {kind:checked?'proof':'tree'in result?'rejected':result.stuck,minimalKind:'sat',fallback:true,minimalUnits,fallbackUnits:units()-minimalUnits,witness:small.witness,...(checked&&'tree'in result?{tree:result.tree}:{})}
}
