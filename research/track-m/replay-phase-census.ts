// Independent of the installed instrumentation and its in-memory leaf caches.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {check} from '../../kernel/kernel.ts'
import {usedHyps} from '../../kernel/prove.ts'
const directory=process.argv[2]!
const verification=JSON.parse(readFileSync(join(directory,'verification.json'),'utf8'))
let leaves=0,checked=0,exact=0
const failures:any[]=[]
for(const file of verification.replay){
 const rows=JSON.parse(readFileSync(join(directory,file.file),'utf8'))
 for(const row of rows){
  leaves++;const path=new Map<string,any>(row.path),valid=check(row.numeric,row.proof,path),used=valid?usedHyps(row.numeric,row.proof,path):new Set<number>()
  if(valid)checked++
  const ids=row.offered.filter((s:any)=>used.has(s.at)).map((s:any)=>s.id).sort((a:string,b:string)=>a.localeCompare(b)),expected=[...row.cited].sort((a:string,b:string)=>a.localeCompare(b))
  const same=JSON.stringify(ids)===JSON.stringify(expected)
  if(same)exact++
  if(!valid||!same)failures.push({file:file.file,leaf:row.id,valid,same,ids,expected})
 }
}
console.log(JSON.stringify({mode:'phase-census-proof-replay',leaves,checked,exact,failures}))
if(failures.length)process.exitCode=1
