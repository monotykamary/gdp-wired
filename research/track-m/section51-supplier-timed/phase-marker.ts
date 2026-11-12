import {renameSync,writeFileSync} from 'node:fs'

/** Observation only: failures never change the prover's control flow. */
export function phaseMarker(path:string,pid=process.pid){
 let sequence=0,failures=0,statusExportFailures=0
 return {
  mark(phase:string):boolean{
   if(!/^[a-z][a-z0-9-]{0,63}$/.test(phase)){failures++;return false}
   const next=++sequence
   try{
    // One atomic, bounded line; the external sampler rejects a different PID.
    writeFileSync(path+'.tmp',`${pid}\t${next}\t${phase}\t${process.hrtime.bigint()}\n`)
    renameSync(path+'.tmp',path)
    return true
   }catch{failures++;return false}
  },
  saveStatus(save:(status:Readonly<{failures:number,statusExportFailures:number}>)=>void):boolean{
   try{save({failures,statusExportFailures});return true}
   catch{failures++;statusExportFailures++;return false}
  },
  get failures(){return failures},
  get statusExportFailures(){return statusExportFailures},
 }
}
