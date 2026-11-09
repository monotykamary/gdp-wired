// Input, import and source-identity preflight; never a measured proof pair.
import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {resolve,join} from 'node:path'
import {tmpdir} from 'node:os'
import {createHash} from 'node:crypto'
const expected:Record<string,string>=JSON.parse(readFileSync('frozen-paxos/checksums.json','utf8'))
for(const [path,hash] of Object.entries(expected))if(createHash('sha256').update(readFileSync(path)).digest('hex')!==hash)throw Error('input hash mismatch: '+path)
const {restore,command,harnessHashes}=await import(resolve('research/verify-all/final-gate-common.ts'))
const input=resolve('paxos-input'),{baseline}=JSON.parse(readFileSync(join(input,'gate.json'),'utf8'))
const points:string[]=JSON.parse(readFileSync('regression-driver/paxos-points.json','utf8'))
const protectedHashes:Record<string,Record<string,string>>=JSON.parse(readFileSync('regression-driver/paxos-harness-hashes.json','utf8'))
const build=await Bun.build({entrypoints:[resolve('regression-driver/paxos-cohort.ts'),resolve('regression-driver/bar-resource-pairs.ts')],target:'bun'})
if(!build.success)throw Error(build.logs.map(message=>message.message).join('; '))
const temp=mkdtempSync(join(tmpdir(),'lane-i-paxos-bootstrap-'))
const restorePoints=process.env.PAXOS_ENDPOINTS_ONLY==='1'?[points[0]!,points.at(-1)!]:points
let restored=0
try{for(const [index,revision] of restorePoints.entries()){
 const dest=join(temp,String(index)),meta=restore(input,dest,revision),hashes=harnessHashes(dest)
 if(Object.keys(hashes).length!==Object.keys(protectedHashes[revision]??{}).length||Object.entries(protectedHashes[revision]??{}).some(([path,hash])=>hashes[path]!==hash))throw Error('protected source mismatch: '+revision)
 if(readFileSync(join(dest,'core/counts.ts'),'utf8').split('return {traced, get counted()').length!==2)throw Error('trace anchor mismatch: '+revision)
 if(index===0||index===restorePoints.length-1)command('bun',['install','--frozen-lockfile'],dest)
 console.log('PAXOS_BOOTSTRAP_RESTORE '+JSON.stringify({meta,hashes}));restored++;rmSync(dest,{recursive:true,force:true})
}}finally{rmSync(temp,{recursive:true,force:true})}
console.log('PAXOS_BOOTSTRAP_PASS '+JSON.stringify({baseline,hashedFiles:Object.keys(expected).length,restored,manifestPoints:points.length,measuredPairs:0}))
