// Original strict-harness pairs only. This is a prerequisite, never a final gate.
import {readFileSync,writeFileSync,mkdtempSync,existsSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {brotliCompressSync,brotliDecompressSync,constants} from 'node:zlib'
import {parseMldrPair} from '../validation-audit.ts'
export const cpu = 'AMD Ryzen 9 9950X 16-Core Processor'
export type Identity = {baseline:string,candidate:string,harness:string,counts:{base:string,candidate:string}}
type Hashes = {harness:string,counts:string}
export type Pair = {repeat:number,exit:number,sha256:string,log:string,hashes:{base:Hashes,candidate:Hashes}}
export type Cohort = {id:number,cpu:string,identity:Identity,pairs:Pair[]}
export const digest = (text:string|Buffer) => createHash('sha256').update(text).digest('hex')
export function checkCohort(group:Cohort,identity:Identity,id:number) {
 const issues:string[]=[]
 if(group.id!==id||group.cpu!==cpu)issues.push('cohort identity/CPU mismatch')
 if(group.identity.baseline!==identity.baseline||group.identity.candidate!==identity.candidate)issues.push('source identity mismatch')
 if(group.pairs.length!==5||new Set(group.pairs.map(pair=>pair.repeat)).size!==5||group.pairs.some(pair=>!Number.isInteger(pair.repeat)||pair.repeat<1||pair.repeat>5))issues.push('five-repeat roster mismatch')
 const pairs=group.pairs.map(pair=>{
  if(pair.exit!==0||digest(pair.log)!==pair.sha256)issues.push(`repeat ${pair.repeat}: exit/raw hash`)
  if(!pair.log.includes(identity.baseline)||!pair.log.includes(identity.candidate))issues.push(`repeat ${pair.repeat}: missing source identity`)
  for(const side of ['base','candidate'] as const){
   if(pair.hashes[side].harness!==identity.harness||pair.hashes[side].counts!==identity.counts[side])issues.push(`repeat ${pair.repeat}: ${side} source hashes`)
  }
  const parsed=parseMldrPair(pair.log,pair.repeat,'consensus_forall')
  issues.push(...parsed.issues.map(issue=>`repeat ${pair.repeat}: ${issue}`))
  return {...parsed,noLoss:parsed.issues.length===0&&parsed.sides.every(side=>side.exit==='0'&&side.result?.search.verdict==='proven'),sha256:pair.sha256}
 })
 return {issues,pairs,noLoss:issues.length===0&&pairs.length===5&&pairs.every(pair=>pair.noLoss)}
}
function run(id:number){
 if(!Number.isInteger(id)||id<1)throw Error('positive cohort id required')
 const model=readFileSync('/proc/cpuinfo','utf8').match(/^model name\s*:\s*(.+)$/m)?.[1]?.trim()??'<missing>'
 if(model!==cpu){console.log('CONSENSUS_CPU_SKIP '+JSON.stringify({id,cpu:model}));return}
 const root=resolve(import.meta.dir,'../../..'),identity=JSON.parse(readFileSync(join(root,'integ-input/identity.json'),'utf8')) as Identity
 const dir=mkdtempSync(join(tmpdir(),`lane-i-consensus-${id}-`)),pairs:Pair[]=[]
 console.log('CONSENSUS_STARTED '+JSON.stringify({id,cpu:model,dir}))
 const hashFile=(path:string)=>existsSync(path)?digest(readFileSync(path)):''
 for(let repeat=1;repeat<=5;repeat++){
  const child=spawnSync('bash',['research/lane-i/validate.sh','mldr',String(repeat),'consensus_forall'],{cwd:root,encoding:'utf8',maxBuffer:32*1024*1024})
  const log=(child.stdout??'')+'\n'+(child.stderr??'')+(child.error?'\n'+String(child.error):'')
  writeFileSync(join(dir,`${repeat}.log`),log)
  const hashes={} as Pair['hashes']
  for(const side of ['base','candidate'] as const){const path=side==='base'?join(root,'base'):root;hashes[side]={harness:hashFile(join(path,'research/protocols/ic3syn/run.ts')),counts:hashFile(join(path,'core/counts.ts'))}}
  pairs.push({repeat,exit:child.status??1,sha256:digest(log),log,hashes})
 }
 const group:Cohort={id,cpu:model,identity,pairs}
 const packed=brotliCompressSync(Buffer.from(JSON.stringify(group)),{params:{[constants.BROTLI_PARAM_QUALITY]:11}})
 const archive=join(dir,'cohort.br');writeFileSync(archive,packed)
 const encoded=packed.toString('base64')
 console.log('CONSENSUS_ARCHIVE '+JSON.stringify({id,path:archive,sha256:digest(packed),encodedBytes:encoded.length}))
 if(encoded.length>350000)throw Error('collector-safe payload bound exceeded; durable archive retained')
 console.log('CONSENSUS_COHORT_BR '+encoded)
 if(pairs.some(pair=>pair.exit!==0))process.exitCode=1
}
function audit(dir:string,identityPath:string,jobsPath:string){
 const identity=JSON.parse(readFileSync(identityPath,'utf8')) as Identity,jobs=JSON.parse(readFileSync(jobsPath,'utf8')) as {name:string}[]
 const rows=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t'))
 const placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),issues:string[]=[],cohorts:unknown[]=[]
 let skips=0,acceptedPairs=0,losses=0
 if(rows.length!==jobs.length||new Set(rows.map(row=>row[0])).size!==jobs.length||rows.some(row=>!jobs.some(job=>job.name===row[0])))issues.push('batch roster mismatch')
 for(const job of jobs){
  try{
   const id=Number(/-(\d+)$/.exec(job.name)?.[1]),p=placement[job.name],row=rows.find(row=>row[0]===job.name),log=readFileSync(join(dir,`${job.name}.log`),'utf8')
   if(row?.[1]!=='0'||row?.[3]!=='boat')issues.push(`${job.name}: failed/non-boat result`)
   const skip=[...log.matchAll(/^CONSENSUS_CPU_SKIP (.+)$/gm)],receipt=[...log.matchAll(/^CONSENSUS_COHORT_BR (\S+)$/gm)]
   if(skip.length){const value=JSON.parse(skip[0]![1]!);if(skip.length!==1||receipt.length||value.id!==id||value.cpu===cpu||value.cpu!==p?.cpu)throw Error('invalid CPU skip');skips++;continue}
   if(receipt.length!==1||p?.cpu!==cpu||p.exclusive!==true||p.co_tenants!==0||p.type!=='large')throw Error('missing receipt or wrong placement')
   const group=JSON.parse(brotliDecompressSync(Buffer.from(receipt[0]![1]!,'base64')).toString()) as Cohort
   const checked=checkCohort(group,identity,id);issues.push(...checked.issues.map(issue=>`${job.name}: ${issue}`))
   if(!checked.issues.length){acceptedPairs+=checked.pairs.length;losses+=checked.pairs.filter(pair=>!pair.noLoss).length}
   cohorts.push({name:job.name,placement:p,sha256:digest(log),...checked})
  }catch(error){issues.push(`${job.name}: ${String(error)}`)}
 }
 const noLoss=issues.length===0&&acceptedPairs>=5&&losses===0
 const report={finalGate:false,identity,issues,skips,acceptedPairs,losses,noLoss,cohorts}
 writeFileSync(join(dir,'consensus-audit.json'),JSON.stringify(report,null,2)+'\n')
 console.log(JSON.stringify({issues,skips,acceptedPairs,losses,noLoss,finalGate:false}))
 if(!noLoss)process.exitCode=1
}
if(import.meta.main){const [mode,...args]=process.argv.slice(2);if(mode==='run')run(Number(args[0]));else if(mode==='audit'&&args.length===3)audit(args[0]!,args[1]!,args[2]!);else throw Error('usage: consensus-recheck.ts run ID | audit DIR IDENTITY JOBS')}
