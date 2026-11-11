// Untrusted discovery for a lifted comparison of stored rows and two halves.
// The generator's provenance supplies the correspondence; no law, protocol,
// operation, flag, or map name is a dispatch key.
import {type Law, type Machine, all, n, same, walkOnce, x} from './machine.ts'
import {discoverRowAgreement, type RowAgreementShape} from './row-agreement-shape.ts'
import {classifyRowValueWrite} from './count-row-policy.ts'
import {finiteCountChoice} from './count-cases.ts'
import {discoverCountGuardShape, type CountGuardShape} from './count-guard-shape.ts'
import {discoverCountRowCopy} from './count-copy-shape.ts'
import {discoverCountThresholdWrite} from './count-write-shape.ts'
import {quorumLawProvenance, type QuorumLawProvenance} from './quorum-laws.ts'
export type LiftedCountGuardShape = {origin: Readonly<QuorumLawProvenance>, countShape: CountGuardShape, countMaps: string[], rowAgreement?: RowAgreementShape, rowAgreements: {law: Law, shape: RowAgreementShape}[]}
export function discoverLiftedCountGuard(m: Machine, law: Law, family: readonly Law[], observe?:(event:Record<string,unknown>)=>void): LiftedCountGuardShape | undefined {
 const origin = quorumLawProvenance(law)
 if (!origin) {
  if(observe&&law.forall&&law.keys?.length===3){
   const maps=new Set<string>(),variables=new Set<string>()
   walkOnce(law.holds,(node:any)=>{if(node.op==='get'&&m.counts?.[node.map])maps.add(node.map);if(node.op==='var')variables.add(node.name)})
   if(maps.size>=3&&law.keys.slice(1).every(key=>variables.has(key)))observe({stage:'lifted-decline',reason:'no provenance',message:'lifted-decline: no provenance'})
  }
  return
 }
 if (!origin.disabled || origin.halves.length !== 2 || !law.forall || law.keys?.length !== 3 || !origin.twins.length) return
 if (!(origin.membershipMap in (m.maps ?? {})) || !m.inputMaps?.includes(origin.requestSet) || !m.inputs.includes(origin.rowInput) || JSON.stringify(m.step.flags?.[origin.guard]) !== origin.guardFormula) return
 if (Object.entries(origin.definitions).some(([name, definition]) => JSON.stringify(m.counts?.[name]) !== definition)) return
 const choices = family.flatMap(candidate => {
  const shape = discoverCountGuardShape(m, candidate, family)
  if (!shape || shape.rowMap !== origin.rowCount || shape.membershipMap !== origin.membershipMap || shape.width !== origin.width) return []
  let size = 0; walkOnce(m.counts![shape.voteMap]!.body, () => {size++})
  return [{shape, size}]
 }).sort((a, b) => b.size - a.size)
 if (!choices.length) return
 const signature = (shape: CountGuardShape) => JSON.stringify([shape.membershipMap, shape.rowMap, shape.memberField, shape.thresholdField, shape.width])
 if (choices.some(choice => signature(choice.shape) !== signature(choices[0]!.shape))) return
 const countMaps = new Set<string>()
 walkOnce(law.holds, (node: any) => {if (node.op === 'get' && m.counts?.[node.map]) countMaps.add(node.map)})
 if (countMaps.size < 3 || !countMaps.has(origin.rowCount) || origin.twins.some(twin => !countMaps.has(twin.row))) return
 const agreements = family.flatMap(candidate => {const row = discoverRowAgreement(m, candidate); return row?.map === origin.membershipMap && row.width === origin.width ? [{law: candidate, shape: row}] : []}).sort((a,b)=>b.shape.markers.length-a.shape.markers.length)
 // Offer the marked row law first; preserve every other match for a checked
 // fallback if a minimal transport query is satisfiable with that premise.
 return {origin, countShape: choices[0]!.shape, countMaps: [...countMaps], rowAgreements: agreements, ...(agreements[0] ? {rowAgreement: agreements[0].shape} : {})}
}
// The stored action's provenance decides replacement, independently of any
// threshold write. The ordinary row-write classifier must agree with it.
function replacementOperation(m:Machine,shape:LiftedCountGuardShape,name:string):{value?:number,stores:boolean}{
 const write=m.step.maps?.[shape.origin.membershipMap]
 let usesGuard=false,usesSet=false
 walkOnce(write,(node:any)=>{if(node.op==='flag'&&node.name===shape.origin.guard)usesGuard=true;if(node.op==='get'&&node.map===shape.origin.requestSet)usesSet=true})
 const values=new Set<number>(),seen=new Set<string>()
 const visit=(condition:import('./machine.ts').C):void=>{
  if(condition.op==='and'){condition.xs.forEach(visit);return}
  if(condition.op==='flag'&&!seen.has(condition.name)){seen.add(condition.name);const nested=m.step.flags?.[condition.name];if(nested)visit(nested);return}
  if(condition.op!=='=')return
  const [variable,value]=condition.a.op==='var'?[condition.a,condition.b]:[condition.b,condition.a]
  if(variable.op==='var'&&variable.name===name&&value.op==='const')values.add(value.value)
 }
 const guard=m.step.flags?.[shape.origin.guard];if(guard)visit(guard)
 return {stores:usesGuard&&usesSet,...(values.size===1?{value:[...values][0]!}:{})}
}
// A fixed-case emitter must classify only that case: its assumption can make
// every other operation unreachable without invalidating the requested one.
export function discoverLiftedCountOperation(m:Machine,shape:LiftedCountGuardShape,value:number,observe?:(event:Record<string,unknown>)=>void){
 const choice=finiteCountChoice(m)
 if(!choice||!choice[1].has(value))return
 const [name,values]=choice,replacement=replacementOperation(m,shape,name)
 const decline=(kind:unknown,reason:string)=>{observe?.({stage:'lifted-decline',reason,guard:shape.origin.guard,value,kind,replacement:replacement.value,writes:m.step.maps?.[shape.origin.membershipMap]});return undefined}
 if(replacement.stores&&(replacement.value===undefined||!values.has(replacement.value)))return decline(undefined,'replacement-operation')
 const branch={name,value},copy=discoverCountRowCopy(m,shape.countShape,branch),write=discoverCountThresholdWrite(m,shape.countShape,branch)
 const fixed={...m,assume:all(...(m.assume?[m.assume]:[]),same(x(name),n(value)))},rowKind=classifyRowValueWrite(fixed,{map:shape.origin.membershipMap,fields:shape.rowAgreement?.fields??[]})
 const replacing=replacement.stores&&replacement.value===value
 if(replacing&&rowKind!=='replacement'||!replacing&&rowKind==='replacement')return decline(rowKind,'replacement-write-disagreement')
 return {name,value,...(replacing?{kind:'threshold-replace' as const,replacement:{guard:shape.origin.guard,input:shape.origin.requestSet},...(write?{write}:{})}:copy?{kind:'copy' as const,copy}:write?{kind:write.increment?'threshold-increment' as const:'threshold-replace' as const,write}:{kind:rowKind??'frame-or-phase' as const})}
}
export function discoverLiftedCountOperations(m:Machine,shape:LiftedCountGuardShape,observe?:(event:Record<string,unknown>)=>void){
 const choice=finiteCountChoice(m);if(!choice)return
 const planned=[]
 for(const value of [...choice[1]].sort((a,b)=>a-b)){
  const operation=discoverLiftedCountOperation(m,shape,value,observe);if(!operation)return
  planned.push(operation)
 }
 return planned
}
