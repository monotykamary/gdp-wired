import {readFileSync,writeFileSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const dir=process.argv[2];if(!dir)throw Error('paired output directory required')
const baseline='8214a543bc44e88d979f9e4457d7370e7e3c122b',candidate='d3adf3c9589ec014a158b6f42ecfb091c999bb43',issues:string[]=[],results:any[]=[],sha=(s:string|Uint8Array)=>createHash('sha256').update(s).digest('hex')
const placement=JSON.parse(readFileSync(join(dir,'placement.json'),'utf8')),backend=JSON.parse(readFileSync(join(dir,'backends.json'),'utf8')),statuses=readFileSync(join(dir,'summary.tsv'),'utf8').trim().split('\n').map(l=>l.split('\t'))
if(statuses.length!==2||backend.where?.boat!==2||backend.fallbacks?.length)issues.push('backend roster')
const paths=['research/protocols/ic3syn/jobs.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts','research/protocols/models.ts','research/protocols/run.ts','core/search.test.ts','core/extract-py.test.ts']
const expected=Object.fromEntries([baseline,candidate].map(rev=>[rev,Object.fromEntries(paths.map(p=>[p,sha(execFileSync('git',['show',`${rev}:${p}`]))]))]))
for(const kind of ['search','fold']as const){
 const name=kind==='search'?'search-timeout-pairs-7007':'fold-timeout-pairs-7007',ms=kind==='search'?5000:60000,file=kind==='search'?'core/search.test.ts':'core/extract-py.test.ts',target=kind==='search'?'an invariant nobody wrote is found and proven, and said as a law':'a loop over a list the request carries: a fold, exact for every length'
 const command=['bun','test','./'+file,...(kind==='fold'?['--test-name-pattern','^'+target+'$']:[])],rows=readFileSync(join(dir,name+'.log'),'utf8').split('\n').filter(l=>l.startsWith('TIMEOUT_PAIR ')).map(l=>JSON.parse(l.slice(13)))
 const status=statuses.find(r=>r[0]===name),place=placement[name]
 if(status?.[1]!=='0'||status?.[3]!=='boat'||!place?.exclusive||place.co_tenants!==0)issues.push(name+': execution')
 if(rows.length!==3||new Set(rows.map(r=>r.repeat)).size!==3)issues.push(name+': repeat cardinality')
 for(const row of rows){
  if(row.case!==kind||row.config.baseline!==baseline||row.config.candidate!==candidate||row.cpu!==place.cpu||row.testTimeoutMs!==ms||JSON.stringify(row.command)!==JSON.stringify(command)||JSON.stringify(row.order)!==JSON.stringify(row.repeat%2?['base','candidate']:['candidate','base']))issues.push(name+': identity/order')
  for(const side of ['base','candidate']as const){
   const rev=side==='base'?baseline:candidate,o=row.outcomes[side],text=gunzipSync(Buffer.from(o.traceGzipBase64,'base64')).toString(),separator='\n---stderr---\n',at=text.indexOf(separator),stdout=text.slice(0,at),stderr=text.slice(at+separator.length)
   if(at<0||sha(stdout)!==o.stdoutSha256||sha(stderr)!==o.stderrSha256)issues.push(name+': trace digest')
   if(row.meta[side].revision!==rev||!row.meta[side].clean||paths.slice(0,5).some(p=>row.hashes[side][p]!==expected[rev]![p])||o.testSha256!==expected[rev]![file])issues.push(name+': source')
   const passed=Number(/(?:^|\n)\s*(\d+) pass\s*(?:\n|$)/.exec(stderr)?.[1]),failed=Number(/(?:^|\n)\s*(\d+) fail\s*(?:\n|$)/.exec(stderr)?.[1]),assertions=Number(/(\d+) expect\(\) calls/.exec(stderr)?.[1]),line=stderr.split('\n').find(l=>l.startsWith('(pass) '+target+' [')),m=line&&/\[([\d.]+)(ms|s)\]/.exec(line),duration=m?Number(m[1])*(m[2]==='s'?1000:1):NaN
   if(o.exit!==0||failed!==0||passed!==(kind==='search'?10:1)||!line||!Number.isFinite(duration)||duration>ms)issues.push(name+': native test result')
   results.push({case:kind,repeat:row.repeat,side,passed,failed,assertions,durationMs:duration})
  }
 }
 if(expected[baseline]![file]!==expected[candidate]![file])issues.push(name+': test changed')
}
const result={baseline,candidate,issues,pairs:6,processes:results,qualified:issues.length===0,reproduced:results.some(r=>r.failed>0),scope:'Isolated unchanged tests only; original full-suite failures remain.',finalGate:false}
writeFileSync(join(dir,'audit.json'),JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result));if(issues.length)process.exitCode=1
