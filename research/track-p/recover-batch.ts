// Recover immutable completed receipts after a local coordinator timeout; do not rerun jobs.
import {readFileSync,writeFileSync,mkdirSync,copyFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const [prefix,out,expected]=process.argv.slice(2)
if(!prefix||!out||!expected)throw new Error('recover-batch PREFIX OUTPUT EXPECTED_ROWS')
type Row={name:string,code:number,seconds:number,placement:Record<string,unknown>}
const rows=readFileSync(prefix+'.rows','utf8').trim().split('\n').filter(Boolean).map(s=>JSON.parse(s) as Row)
if(rows.length!==Number(expected)||new Set(rows.map(r=>r.name)).size!==rows.length)throw new Error('incomplete or duplicate receipts')
mkdirSync(out,{recursive:true})
const provenance=[]
for(const row of rows){
 const source=prefix+'.logs/'+row.name,a=readFileSync(source+'/out'),b=readFileSync(source+'/err')
 copyFileSync(source+'/out',out+'/'+row.name+'.out');copyFileSync(source+'/err',out+'/'+row.name+'.err')
 writeFileSync(out+'/'+row.name+'.log',a.toString()+(b.length?'\n\n--- stderr ---\n'+b.toString():''))
 provenance.push({name:row.name,stdoutSha256:createHash('sha256').update(a).digest('hex'),stderrSha256:createHash('sha256').update(b).digest('hex')})
}
writeFileSync(out+'/summary.tsv',rows.map(r=>`${r.name}\t${r.code}\t${r.seconds}\tboat`).join('\n')+'\n')
writeFileSync(out+'/placement.json',JSON.stringify(Object.fromEntries(rows.map(r=>[r.name,r.placement])),null,1)+'\n')
writeFileSync(out+'/recovery.json',JSON.stringify({source:prefix,recoveredAt:new Date().toISOString(),note:'The local coordinator expired after 1000 seconds. All expected worker receipts were already durable; no job was rerun.',provenance},null,1)+'\n')
console.log(JSON.stringify({out,recovered:rows.length}))
