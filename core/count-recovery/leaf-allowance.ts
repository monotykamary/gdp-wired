/** One even share of the still-unspent goal allowance, capped at one third.
 * Split children receive the same absolute deadline; the second spends only
 * what the first leaves. Unspent allowance is retained, not a final-leaf bonus. */
export const leafAllowance=(remaining:number,leavesLeft:number):number=>{
 const available=Math.max(0,remaining)
 return Math.min(available/Math.max(1,leavesLeft),available/3)
}
