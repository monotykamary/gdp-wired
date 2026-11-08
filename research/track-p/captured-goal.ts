import {readFileSync} from 'node:fs'
import {gunzipSync,gzipSync} from 'node:zlib'
import {type Goal,checkMC} from '../../kernel/kernel.ts'
import {grow,clock,counted,fullRate,withWall,withDeadline,widen} from '../../kernel/prove.ts'
import {relevantGoals} from '../../core/relevance.ts'
const text=readFileSync(process.argv[2]!,'utf8'),encoded=text.match(/^FAILURES_GZIP (\S+)/m)?.[1]
if(!encoded)throw Error('missing retained failure packet')
const rows=JSON.parse(gunzipSync(Buffer.from(encoded,'base64')).toString()),row=rows.find((r:any)=>r.index===Number(process.argv[3])),snap=row?.first
if(!snap?.hyps||!snap.raw)throw Error('missing exact first decision query')
const goal:Goal={name:snap.raw.name,hyps:snap.hyps},parts=[goal,...relevantGoals(goal)]
for(const [index,part]of parts.entries()){
 const start=performance.now(),result=withWall(start+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>grow(part,new Map(),{nodes:0,until:clock()+1500})),true))
 const tree='tree'in result?widen(part,goal,result.tree):undefined,cert=tree?{...snap.certificateRequest,tree}:undefined,checked=!!cert&&checkMC(snap.raw.hyps,snap.decls,cert)
 console.log(JSON.stringify({index,hyps:part.hyps.length,status:'tree'in result?'tree':result.stuck,checked,ms:performance.now()-start}))
 if(tree&&!checked)throw Error('captured proof failed original MC check')
 if(checked)console.log('CERT_GZIP '+gzipSync(JSON.stringify({goal:{raw:snap.raw,decls:snap.decls},proof:cert})).toString('base64'))
}
