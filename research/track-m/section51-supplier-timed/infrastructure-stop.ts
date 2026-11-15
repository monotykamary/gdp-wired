// Raw native infrastructure receipts never become a proof/search verdict.
export function infrastructureStop(rows:any,guard:any){
 const names=['mldr-3g-timed','mldr-3g-instrumented']
 const affected=names.flatMap(name=>{
  const row=rows?.[name];if(!row)return []
  const code=row.code,elapsed=row.seconds
  if(code===124&&typeof elapsed==='number'&&Number.isFinite(elapsed)&&elapsed>=guard.effectivePayloadGuardSeconds-1)
   return [{name,label:'INFRA_HANG_GUARD',rawNativeRow:row,originalSignal:'NOT_EXPORTED',deadlineAttribution:'native normalized timeout at/beyond the external guard'}]
  if(code===124||code===137||code===-9||['LOST','PREEMPTED','CANCELLED'].includes(row.status))
   return [{name,label:'INFRASTRUCTURE_TERMINATION_UNATTRIBUTED',rawNativeRow:row,originalSignal:'NOT_INFERRED',deadlineAttribution:'code alone does not establish that the external guard fired; retain stderr/OOM/custody'}]
  return []
 })
 if(!affected.length)return undefined
 return {status:affected.some(a=>a.label==='INFRA_HANG_GUARD')?'INFRA_HANG_GUARD':'INFRASTRUCTURE_TERMINATION_UNATTRIBUTED',verdict:null,proofVerdict:null,affected,guard,evidenceStatus:'RAW_NATIVE_RECEIPT_REQUIRES_CUSTODY_REVIEW',note:'Infrastructure only: no unknown/refuted/proven result is inferred. Partial artifacts and the other arm remain retained; no retry.'}
}
