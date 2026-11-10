// Observe counters outside the timed law calls; the existing family harness,
// including its final checkMC, is imported byte-for-byte unchanged on both sides.
export {}
const hooks=await import('../../core/count-recovery/conditional-proof.ts')
const stats=(hooks as {conditionalProofStats?:()=>Readonly<Record<string,number>>}).conditionalProofStats
let before=stats?.()
const log=console.log.bind(console)
console.log=(...args:unknown[])=>{
 log(...args)
 if(typeof args[0]!=='string')return
 let row:any
 try{row=JSON.parse(args[0])}catch{return}
 if(row.mode!=='family')return
 const after=stats?.(),delta=after&&Object.fromEntries(Object.entries(after).map(([k,v])=>[k,v-(before?.[k]??0)]))
 log(JSON.stringify({mode:'cost-win-stats',law:row.law,stats:delta??null}))
 before=after
}
try{await import('./profile-family.ts')}finally{console.log=log}
