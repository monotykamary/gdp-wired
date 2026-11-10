// Receipt formatting only: no search, build, test or inference. Safe to run locally.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const dir='runs/t16-tiny-worker-wrapper-v7',capture=JSON.parse(readFileSync('runs/t16-frontier-capture/0.json','utf8'))
const names=(capture.beforeFinite.candidates as {name:string}[]).map(l=>l.name)
const placement=JSON.parse(readFileSync(`${dir}/placement.json`,'utf8'))
const summary=readFileSync(`${dir}/summary.tsv`,'utf8').trim().split('\n').map(line=>line.split('\t'))
if(summary.length!==6||new Set(summary.map(row=>row[0])).size!==6)throw Error('unexpected or duplicate measured roster')
const runs=[]
for(const mode of ['original40','survivors34'])for(const n of [1,2,3]){
  const job=`tiny-${mode}-${n}`,text=readFileSync(`${dir}/${job}.log`,'utf8')
  const lines=text.split('\n').filter(s=>s.startsWith('TINY_WRAPPER_RESULT '))
  if(lines.length!==1)throw Error('missing/duplicate receipt: '+job)
  const r=JSON.parse(lines[0]!.slice(20)),removed=new Set<string>([...r.historical,...r.drops.map((d:{law:string})=>d.law)])
  const side=summary.find(row=>row[0]===job),exitCode=Number(side?.[1])
  if(!side||exitCode!==(r.drops.length>=5?0:1))throw Error('unexpected side exit: '+job)
  if(r.mode!==(mode==='original40'?'original':'survivors')||r.initial!==(mode==='original40'?40:34))throw Error('family/input mode mismatch: '+job)
  if(r.finish.dropped!==r.drops.length||r.survivors!==r.initial-r.drops.length)throw Error('inconsistent drop count: '+job)
  if(!placement[job]?.exclusive||placement[job]?.co_tenants!==0)throw Error('missing exclusive placement: '+job)
  runs.push({job,exitCode,hardware:placement[job],...r,remainingCandidates:names.filter(name=>!removed.has(name))})
}
const owned=['core/finite-tiny.ts','core/finite-tiny.test.ts','research/track-gen/t16-tiny-wrapper-bench.ts']
const input={path:'runs/t16-frontier-capture/0.json',sha256:createHash('sha256').update(readFileSync('runs/t16-frontier-capture/0.json')).digest('hex'),callerNames:(capture.beforeFinite.caller as {name:string}[]).map(l=>l.name),candidateNames:names}
const result={input,batch:'20261109-144230-03co60',measuredTree:'f1a9b896a1a8',trust:'Untrusted finite screens; drops independently certified by Main finiteTinyHoudini pre/facts/full-family/source interpreter/post-law checks. Not proofs or semantic exhaustion.',validation:{batch:'20261109-145638-3wrrd7',log:'runs/t16-tiny-worker-final-check/tiny-unit-and-check.log',tests:12,assertions:40,typecheckAndLint:'pass'},ownedSha256:Object.fromEntries(owned.map(path=>[path,createHash('sha256').update(readFileSync(path)).digest('hex')])),runs}
writeFileSync('research/track-gen/t16-tiny-results.json',JSON.stringify(result,null,2)+'\n')
for(const r of runs)console.log(JSON.stringify({job:r.job,initial:r.initial,remainingFamily:r.survivors,certified:r.drops.map((d:{law:string})=>d.law),finish:r.finish,lastRound:r.rounds.at(-1)?.stats.exhausted,unsupported:r.rounds.flatMap((x:{stats:{unsupported:string[]}})=>x.stats.unsupported)}))
