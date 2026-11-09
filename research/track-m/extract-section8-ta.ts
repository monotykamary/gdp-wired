// Decode only whitelisted data receipts; never evaluate log contents.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [file,dir]=process.argv.slice(2);if(!file||!dir)throw new Error('LOG OUTPUT_DIR required')
mkdirSync(dir,{recursive:true});const results:any[]=[],seen=new Set<string>()
for(const line of readFileSync(file,'utf8').split('\n')){
 if(!line.startsWith('{'))continue
 const row=JSON.parse(line)
 if(row.encoding!=='gzip-base64'||!['ta-data.log','ta-star.log','ta-overlap.log'].includes(row.artifact))continue
 if(seen.has(row.artifact))throw new Error('duplicate receipt');seen.add(row.artifact)
 const text=gunzipSync(Buffer.from(row.data,'base64')).toString('utf8');writeFileSync(join(dir,row.artifact),text)
 for(const line of text.split('\n')){
  if(!line.startsWith('{'))continue
  const item=JSON.parse(line)
  if(item.test==='T-A')results.push(item)
  if(item.artifact==='T-A-leaf'&&item.encoding==='gzip-base64')writeFileSync(join(dir,item.law.startsWith('Inv*')?'Invstar-leaf.json':'Inv2973-leaf.json'),gunzipSync(Buffer.from(item.data,'base64')))
 }
}
writeFileSync(join(dir,'results.json'),JSON.stringify(results,null,2)+'\n')
console.log(JSON.stringify(results.map(r=>({...r,path:undefined,model:undefined,query:r.query&&{wallMs:r.query.wallMs,countedUnits:r.query.countedUnits,numericChecked:r.query.numericChecked,conditionalChecked:r.query.conditionalChecked,outcome:'tree'in r.query.q?'tree':r.query.q.stuck,why:r.query.q.why},attempts:r.attempts.map((a:any)=>({...a,source:undefined,path:undefined,model:undefined,lemma:a.lemma?{when:a.lemma.when,cut:a.lemma.cut}:undefined}))})),null,2))
