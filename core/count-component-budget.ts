// Pure remaining-pool allocation. The caller supplies an already-clamped
// component endpoint; this helper never creates a new root or tier grant.
export function countComponentAttemptBudget(now:number,componentEnd:number,unattempted:number,minimum=1,fair=false){
 if(!Number.isFinite(now)||!Number.isFinite(componentEnd)||!Number.isInteger(unattempted)||unattempted<1||!Number.isFinite(minimum)||minimum<0)throw new RangeError('invalid component allowance')
 const width=Math.max(0,componentEnd-now),floor=Math.min(minimum,width/unattempted)
 const reserved=fair?width-width/unattempted:floor*(unattempted-1),allotted=fair?width/unattempted:Math.max(0,width-reserved)
 return {end:Math.min(componentEnd,now+allotted),allotted,reserved}
}
