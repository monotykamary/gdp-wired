import {expect,test} from 'bun:test'
import {mkdtempSync,rmSync,readFileSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {fileURLToPath} from 'node:url'
test('R3 phase-status-only failure leaves verdict artifacts and process exit unchanged',()=>{
 const root=mkdtempSync(join(tmpdir(),'phase-status-')),script=fileURLToPath(new URL('./phase-status.fixture.ts',import.meta.url))
 try{
  for(const mode of ['ok','fault']){
   const out=join(root,mode),run=Bun.spawnSync([process.execPath,script,out,mode])
   expect(run.exitCode).toBe(0)
   expect(JSON.parse(readFileSync(join(out,'verdict.json'),'utf8'))).toEqual({proven:true,checked:true})
   const telemetry=JSON.parse(readFileSync(join(out,'telemetry.json'),'utf8'))
   expect(telemetry.phaseStatusExported).toBe(mode==='ok');expect(telemetry.statusExportFailures).toBe(mode==='ok'?0:1)
  }
 }finally{rmSync(root,{recursive:true,force:true})}
})
