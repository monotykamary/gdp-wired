// Collector-only negative controls, not source-law fixtures. Run after positive receipt verification.
import {mkdtempSync,readFileSync,readdirSync,symlinkSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const [verifier,source,receipts,temp,expected]=process.argv.slice(2)
if(!verifier||!source||!receipts||!temp||!expected)throw Error('negative controls need all five arguments')
const rows=readFileSync(join(receipts,'summary.tsv'),'utf8').trim().split('\n')
const cases=[
 {name:'missing-job',rows:rows.slice(1),message:'supplement missing, duplicate, failed or non-Boat job'},
 {name:'duplicate-job',rows:[rows[0]!,...rows.slice(0,-1)],message:'supplement missing, duplicate, failed or non-Boat job'},
 {name:'non-boat-job',rows:rows.map((r,i)=>i===0?r.replace(/\tboat(?:\t|$)/,'\tmodal'):r),message:'supplement missing, duplicate, failed or non-Boat job'},
 {name:'failed-job',rows:rows.map((r,i)=>i===0?r.replace(/\t0\t/,'\t1\t'):r),message:'supplement missing, duplicate, failed or non-Boat job'},
]
for(const test of cases){
 const dir=mkdtempSync(join(temp,'negative-'))
 for(const name of readdirSync(receipts))if(name!=='summary.tsv')symlinkSync(join(receipts,name),join(dir,name))
 writeFileSync(join(dir,'summary.tsv'),test.rows.join('\n')+'\n')
 const p=Bun.spawnSync(['bun',verifier,source,dir,join(temp,'negative-decoded'),expected],{stdout:'pipe',stderr:'pipe'})
 const text=p.stdout.toString()+p.stderr.toString()
 if(p.exitCode===0||!text.includes(test.message))throw Error('collector negative control did not reject for intended reason: '+test.name)
 console.log('SUPPLEMENT_NEGATIVE_CONTROL '+JSON.stringify({name:test.name,rejected:true}))
}
console.log('SUPPLEMENT_NEGATIVE_CONTROLS_VERIFIED 4')
