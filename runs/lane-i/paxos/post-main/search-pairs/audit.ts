import {readFileSync,writeFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir=import.meta.dir,text=readFileSync(dir+'/search-pairs-6601.log','utf8'),rows=text.split('\n').filter(line=>line.startsWith('SEARCH_PAIR ')).map(line=>JSON.parse(line.slice(12)))
const baseline='8214a543bc44e88d979f9e4457d7370e7e3c122b',candidate='d3adf3c9589ec014a158b6f42ecfb091c999bb43',placement=JSON.parse(readFileSync(dir+'/placement.json','utf8'))['search-pairs-6601'],backend=JSON.parse(readFileSync(dir+'/backends.json','utf8')),status=readFileSync(dir+'/summary.tsv','utf8').trim().split('\t'),issues:string[]=[],summaries:any[]=[]
const digest=(s:string)=>createHash('sha256').update(s).digest('hex')
if(rows.length!==3||new Set(rows.map(row=>row.repeat)).size!==3)issues.push('repeat roster')
if(status[0]!=='search-pairs-6601'||status[1]!=='0'||status[3]!=='boat'||backend.where?.boat!==1||backend.fallbacks?.length||!placement?.exclusive||placement.co_tenants!==0)issues.push('execution/placement')
const expected=JSON.parse(readFileSync('research/lane-i/regressions/paxos-harness-hashes.json','utf8'))
for(const row of rows){
 if(row.config.baseline!==baseline||row.config.candidate!==candidate||row.defaultTestTimeoutMs!==5000||row.cpu!==placement.cpu||JSON.stringify(row.command)!==JSON.stringify(['bun','test','./core/search.test.ts'])||JSON.stringify(row.order)!==JSON.stringify(row.repeat%2?['base','candidate']:['candidate','base']))issues.push('identity/command/order')
 for(const side of ['base','candidate']){
  const revision=side==='base'?baseline:candidate,o=row.outcomes[side],raw=gunzipSync(Buffer.from(o.traceGzipBase64,'base64')).toString(),separator='\n---stderr---\n',at=raw.indexOf(separator),stdout=raw.slice(0,at),stderr=raw.slice(at+separator.length)
  if(at<0||digest(stdout)!==o.stdoutSha256||digest(stderr)!==o.stderrSha256)issues.push(row.repeat+'/'+side+': raw trace')
  if(row.meta[side].revision!==revision||!row.meta[side].clean||Object.keys(row.hashes[side]).length!==Object.keys(expected[revision]).length||Object.entries(expected[revision]).some(([path,hash])=>row.hashes[side][path]!==hash))issues.push(row.repeat+'/'+side+': source')
  const passed=Number(/(?:^|\n)\s*(\d+) pass\s*(?:\n|$)/.exec(stderr)?.[1]),failed=Number(/(?:^|\n)\s*(\d+) fail\s*(?:\n|$)/.exec(stderr)?.[1]),assertions=Number(/(\d+) expect\(\) calls/.exec(stderr)?.[1]),target=stderr.split('\n').find(line=>line.startsWith('(pass) an invariant nobody wrote is found and proven'))
  if(o.exit!==0||!passed||failed!==0||!target)issues.push(row.repeat+'/'+side+': test failure')
  summaries.push({repeat:row.repeat,side,exit:o.exit,passed,failed,assertions,wallMs:o.wallMs,target})
 }
}
const result={issues,baseline,candidate,cpu:placement.cpu,pairs:rows.length,processes:summaries,unchangedTestTimeoutMs:5000,qualified:issues.length===0,reproduced:summaries.some(row=>row.exit!==0||row.failed>0),scope:'Isolated paired test only; full-suite confirmation still separate.',finalGate:false}
writeFileSync(dir+'/pair-audit.json',JSON.stringify(result,null,2)+'\n');console.log(JSON.stringify(result));if(issues.length)process.exitCode=1
