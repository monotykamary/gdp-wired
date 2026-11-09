// Receipt/provenance audit only. Never promotes a conditional STEP to a whole proof.
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {parseUpperLog} from './summarize.ts'
export function elapsedSeconds(text:string):number|undefined{
 const raw=/Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)/.exec(text)?.[1]
 return raw?.split(':').reduce((total,part)=>total*60+Number(part),0)
}
export function stopKind(status:string,terminal:boolean,exit:number|undefined,elapsed:number|undefined){
 if(status!=='censored')return status
 if(terminal)return 'cooperative-wall'
 if(elapsed!==undefined&&elapsed>=1805&&(exit===124||exit===137||exit===143))return 'watchdog'
 if(exit===137||exit===143)return 'early-process-kill'
 return 'other-nonterminal'
}
const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
if(import.meta.main){
 const [dir,input]=process.argv.slice(2);if(!dir||!input)throw new Error('usage: audit.ts result-dir frozen-input-dir')
 const identity=JSON.parse(readFileSync(join(input,'identity.json'),'utf8')),source=readFileSync(join(input,'source.sha256'),'utf8'),family=readFileSync(join(input,'family.json'),'utf8')
 const manifest=new Map(source.trim().split('\n').map(line=>{const [sha,...path]=line.split(/\s+/);return[path.join(' '),sha]}))
 const jobs:{name:string}[]=JSON.parse(readFileSync(new URL('./resume.jobs.json',import.meta.url),'utf8')),status=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(line=>line.split('\t')),placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),backend=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8')),issues:string[]=[],signatures=new Map<string,string>()
 if(hash(source)!==identity.sourceManifestSha256||hash(family)!==identity.familySha256)issues.push('frozen input hash mismatch')
 if(status.length!==140||jobs.length!==140||new Set(status.map(row=>row[0])).size!==140)issues.push('invalid 140-shard roster')
 if(backend.where?.boat!==140||backend.fallbacks?.length)issues.push('non-boat or fallback execution')
 const rows=jobs.map(job=>{
  const local:string[]=[],fail=(ok:boolean,message:string)=>{if(!ok)local.push(message)},text=readFileSync(join(dir,job.name+'.log'),'utf8'),parsed=parseUpperLog(text),p=placement[job.name],s=status.filter(row=>row[0]===job.name),parts=/^(star|half|rows|p1|safety)-op([0-6])-p([01])-(on|off)$/.exec(job.name)
  if(!parts)throw new Error('bad job name '+job.name)
  fail(s.length===1&&s[0]![1]==='0'&&s[0]![3]==='boat','failed scheduler result')
  fail(p?.exclusive===true&&p.co_tenants===0&&p.type==='large','invalid placement')
  const read=(prefix:string)=>text.split('\n').filter(line=>line.startsWith(prefix+' ')).map(line=>JSON.parse(line.slice(prefix.length+1)))
  const metadata=[...read('UPPER_PROGRESS'),...read('UPPER_RESULT'),...read('UPPER_CENSORED')],patches=read('UPPER_PATCHES'),verify=read('UPPER_VERIFY'),exits=[...text.matchAll(/^UPPER_PROCESS_EXIT (\d+)$/gm)],exit=exits.length===1?Number(exits[0]![1]):undefined
  fail(metadata.length>0,'missing research metadata')
  for(const m of metadata){
   fail(m.sourceSha===identity.sourceSha&&m.familyHash===identity.familySha256,'source/family identity mismatch')
   fail(m.tag===parts[1]&&m.operation?.name==='op'&&m.operation.value===Number(parts[2])&&m.pass===Number(parts[3])&&m.ceilings===parts[4],'shard metadata mismatch')
   fail(m.researchOnly===true&&m.originalFamily===true&&m.noShare===true&&m.familySize===34&&Array.isArray(m.suppliedLaws)&&m.suppliedLaws.length===0,'original-family contract mismatch')
   fail(m.countedBudget===1e12&&m.wallLimitMs===1800000&&m.conditional==='original STEP under operation equality','experimental budget/scope mismatch')
   fail(typeof m.cpu==='string'&&m.cpu.replace(/^model name\s*:\s*/,'')===p?.cpu,'CPU metadata mismatch')
  }
  for(const path of manifest.keys())fail(text.split('\n').includes(path+': OK'),'source manifest not checked: '+path)
  fail(patches.length===1&&patches[0]?.ceilings===parts[4],'missing or wrong patch receipt')
  const patch=patches[0],sig=JSON.stringify(patch?.files)
  if(signatures.has(parts[4]!))fail(signatures.get(parts[4]!)===sig,'inconsistent disposable patches');else signatures.set(parts[4]!,sig)
  for(const f of patch?.files??[])fail(f.path.startsWith('core/')&&manifest.get(f.path)===f.before&&/^[a-f0-9]{64}$/.test(f.after),'invalid patch source/hash')
  fail(exits.length===1&&exit!==undefined&&[0,124,137,143].includes(exit),'missing or invalid proof-process exit')
  if(parsed.status==='closed')fail(verify.length===1&&verify[0].checked===true&&/^[a-f0-9]{64}$/.test(verify[0].sha256)&&verify[0].conditional==='original STEP under operation equality','missing independent verifier linkage')
  local.push(...parsed.issues);issues.push(...[...new Set(local)].map(issue=>({shard:job.name,issue})).map(row=>JSON.stringify(row)))
  const elapsed=elapsedSeconds(text)
  return{name:job.name,status:parsed.status,stop:stopKind(parsed.status,!!parsed.result,exit,elapsed),proofProcessExit:exit,processSeconds:elapsed,progressWallMs:parsed.wallMs,countedUnits:parsed.countedUnits,workIsLowerBound:parsed.countedUnitsLowerBound,peakRssKiB:parsed.peakRssKiB,lastStage:parsed.lastEvent?.stage??parsed.lastEvent?.phase,excludedCount:parsed.excludedCount,verifier:verify[0],cpu:p?.cpu,logSha256:hash(text)}
 })
 const counts=Object.fromEntries([...new Set(rows.map(row=>row.stop))].map(stop=>[stop,rows.filter(row=>row.stop===stop).length]))
 const report={researchOnly:true,source:identity,scope:'Conditional original-family STEP receipts only; proof artifacts were checked by fresh processes on guests, not replayed locally.',batch:backend.boat?.batch,issues,counts,rows}
 writeFileSync(join(dir,'provenance-audit.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({issues,counts,rows:rows.length}));if(issues.length)process.exitCode=1
}
