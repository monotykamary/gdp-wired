// Untrusted F15 scheduling proposal. A factor match supplies an existing law,
// never a count inequality, a proof, or permission to bypass native checking.
import {type C,type Law,type Machine,all,get,ite,less,n,plus,times,x} from './machine.ts'
import {countsForReads} from './count-facts.ts'
import {discoverCountGuardShape} from './count-guard-shape.ts'
import {discoverLiftedCountGuard} from './count-lifted-shape.ts'
import {matchLiftedCountBodies} from './count-lifted-transports.ts'
import {type Count,substE} from '../kernel/kernel.ts'
export type LiftedCountPrerequisite={law:Law,disabledMap:string,voteMap:string,kind:'diagonal'|'threshold-factor',disabled:Count,votes:Count,threshold?:C,bodyNodes:number}
const json=(value:unknown)=>JSON.stringify(value)
export function liftedCountBodySize(value:unknown):number{
 if(!value||typeof value!=='object')return 0
 if(Array.isArray(value))return value.reduce((sum,child)=>sum+liftedCountBodySize(child),0)
 return ('op'in value?1:0)+Object.values(value).reduce<number>((sum,child)=>sum+liftedCountBodySize(child),0)
}
const atoms=(c:C):C[]=>c.op==='and'?c.xs.flatMap(atoms):[c]
export function discoverLiftedCountPrerequisites(m:Machine,law:Law,family:readonly Law[]):LiftedCountPrerequisite[]{
 const shape=discoverLiftedCountGuard(m,law,family);if(!shape||!law.forall)return []
 const twins=new Set(shape.origin.twins.map(twin=>twin.row)),disabledMaps=shape.countMaps.filter(map=>map!==shape.origin.rowCount&&!twins.has(map))
 if(disabledMaps.length!==1)return []
 const disabledMap=disabledMaps[0]!,row=x(law.forall),decls=Object.entries(m.counts??{}).map(([map,definition])=>({...definition,map}))
 const raw=countsForReads(decls,[['disabled',disabledMap,row]])?.[0];if(!raw)return []
 let member='prerequisite$member';const scope=json([m,law]);while(scope.includes(member))member='$'+member
 const canonical=(count:Count):Count=>({...count,key:member,body:substE(count.body,{vars:{[count.key]:x(member)},maps:{},flags:{}})})
 const disabled=canonical(raw),bodyNodes=liftedCountBodySize(raw.body)
 return family.flatMap<LiftedCountPrerequisite>(candidate=>{
  const guard=discoverCountGuardShape(m,candidate,family)
  if(!guard||guard.rowMap!==shape.origin.rowCount||guard.width!==shape.origin.width)return []
  const rawVotes=countsForReads(decls,[['votes',guard.voteMap,plus(times(guard.width,row),row)]])?.[0];if(!rawVotes)return []
  const votes=canonical(rawVotes),base={law:candidate,disabledMap,voteMap:guard.voteMap,disabled,votes,bodyNodes}
  if(matchLiftedCountBodies(disabled,votes))return [{...base,kind:'diagonal' as const}]
  if(votes.body.op!=='if'||json(votes.body.then)!==json(n(1))||json(votes.body.else)!==json(n(0)))return []
  const threshold=less(get(guard.memberField,x(member)),get(guard.thresholdField,row)),parts=atoms(votes.body.c)
  if(parts.filter(part=>json(part)===json(threshold)).length!==1)return []
  const residual={...votes,body:ite(all(...parts.filter(part=>json(part)!==json(threshold))),n(1),n(0))}
  return matchLiftedCountBodies(disabled,residual)?[{...base,kind:'threshold-factor' as const,threshold}]:[]
 })
}
