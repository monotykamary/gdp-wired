// File-only accounting of the retained integrated run. No proof search.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
type Q={kind:string,name:string,hyps:number,ms:number,work:number,outcome:string,why?:string}
const root=process.argv[2]??'runs/track-p-fast-v1',logFile=process.argv[3]??'capture.log',text=(path:string)=>readFileSync(path,'utf8')
const ledger=text(root+'/dump/queries.jsonl'),qs=ledger.trim().split('\n').map(l=>JSON.parse(l) as Q),log=text(root+'/'+logFile)
const result=JSON.parse(log.split('\n').find(l=>l.startsWith('{"id":"paxos_epr"'))!) as {search:{ms:number}}
const aggregate=(rows:Q[])=>({queries:rows.length,wallMs:rows.reduce((n,q)=>n+q.ms,0),work:rows.reduce((n,q)=>n+q.work,0)})
const attempts=[...log.matchAll(/^counts: try (.+?) \| ls (\d+) pass (\d+) ms ([\d.]+) took ([\d.]+) wall ([\d.]+)(.*?) -> (.+)$/gm)].map(m=>({name:m[1]!,laws:+m[2]!,pass:+m[3]!,budget:+m[4]!,countedMs:+m[5]!,wallMs:+m[6]!,phases:m[7]!,outcome:m[8]!}))
const grouped=Object.fromEntries(['tree','unknown','sat'].map(outcome=>[outcome,aggregate(qs.filter(q=>q.outcome===outcome))]))
const total=aggregate(qs),attemptMs=attempts.reduce((n,a)=>n+a.wallMs,0)
const out={runWallMs:result.search.ms,queryLedgerSHA256:createHash('sha256').update(ledger).digest('hex'),rootQueries:total.queries,queryWallMs:total.wallMs,byOutcome:grouped,byKind:Object.fromEntries([...new Set(qs.map(q=>q.kind))].map(kind=>[kind,aggregate(qs.filter(q=>q.kind===kind))])),outsideQueriesMs:result.search.ms-total.wallMs,traceAttempts:attempts.length,tracedAttemptWallMs:attemptMs,outsideTracedAttemptsMs:result.search.ms-attemptMs,insideAttemptsOutsideQueriesMs:attemptMs-total.wallMs,generationWallMs:null,generationObservation:'Not wall-timestamped in this retained run. candidates at 0 ms uses counted clock(), not performance.now(); do not infer zero wall time.',top10:qs.map((q,index)=>({index,...q})).sort((a,b)=>b.ms-a.ms).slice(0,10),openStepQueries:Object.fromEntries([7,10,11,17,33,66].map(index=>[index,[]]))}
writeFileSync(root+'/timing-accounting.json',JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify(out,null,2))
