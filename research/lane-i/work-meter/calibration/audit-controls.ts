import {strict as assert} from 'node:assert'
import {mkdtempSync,readFileSync,writeFileSync,copyFileSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve(process.argv[2]!),script=join(import.meta.dir,'audit.ts'),temp=mkdtempSync('/tmp/phase-audit-control-')
const run=(folder:string)=>spawnSync(process.execPath,[script,folder],{encoding:'utf8',timeout:10000,maxBuffer:1048576})
try{
 const positive=run(input);assert.equal(positive.status,0,positive.stderr);console.log(positive.stdout.trim())
 const edits:Record<string,(row:any)=>void>={
  duplicateCase:row=>{row.cases[1]=row.cases[0]},
  mixedWeights:row=>{row.diagnosticWeights.epr=2},
  changedRawSignature:row=>{row.cases[0].signatureSha256='0'.repeat(64)},
  wrongSource:row=>{row.source='0'.repeat(40)}
 }
 for(const [name,edit]of Object.entries(edits)){
  for(const file of ['summary.tsv','mini-phase-contract-1.log','mini-phase-contract-2.log','mini-phase-contract-3.log'])copyFileSync(join(input,file),join(temp,file))
  const file=join(temp,'mini-phase-contract-2.log'),text=readFileSync(file,'utf8')
  const old=text.split('\n').find(line=>line.startsWith('MINI_PHASE_CONTRACT '));assert(old)
  const row=JSON.parse(old.slice('MINI_PHASE_CONTRACT '.length));edit(row)
  writeFileSync(file,text.replace(old,'MINI_PHASE_CONTRACT '+JSON.stringify(row)))
  const failure=run(temp);assert.equal(failure.signal,null);assert.notEqual(failure.status,0,name)
 }
 console.log('MINI_PHASE_AUDIT_CONTROLS '+JSON.stringify({passed:true,positive:1,negative:Object.keys(edits)}))
}finally{rmSync(temp,{recursive:true,force:true})}
