import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {auditCostWins} from './cost-wins-audit.ts'
const [file,out]=process.argv.slice(2);if(!file||!out)throw new Error('LOG OUT required')
mkdirSync(out,{recursive:true})
for(const line of readFileSync(file,'utf8').split('\n')){
 if(!line.startsWith('{'))continue
 const r=JSON.parse(line)
 if(r.encoding==='gzip-base64'&&/^(?:[AB][1-3]\.(?:log|stderr\.log)|manifest\.json|measurements\.json|summary\.json)$/.test(r.artifact))writeFileSync(join(out,r.artifact),gunzipSync(Buffer.from(r.data,'base64')))
}
const runs=JSON.parse(readFileSync(join(out,'measurements.json'),'utf8')),manifest=JSON.parse(readFileSync(join(out,'manifest.json'),'utf8')),audit=auditCostWins(runs,manifest)
writeFileSync(join(out,'audit.json'),JSON.stringify(audit,null,2)+'\n')
console.log(JSON.stringify(audit,null,2))
