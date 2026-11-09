import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const dir=process.argv[2];if(!dir)throw new Error('DIR required')
for(const line of readFileSync(join(dir,'calibration.log'),'utf8').split('\n')){if(!line.startsWith('{'))continue;const r=JSON.parse(line);if(r.encoding==='gzip-base64'&&['census-control.log','census-control.stderr.log','environment.txt'].includes(r.artifact))writeFileSync(join(dir,r.artifact),gunzipSync(Buffer.from(r.data,'base64')))}
const rows=readFileSync(join(dir,'census-control.log'),'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)).filter(r=>r.mode==='phase-census')
if(rows.length!==5||rows.some(r=>r.profiled||r.entry!=='focused'))throw new Error('incomplete or instrumented calibration')
const summary=rows.map(r=>({law:r.law,proven:r.proven,checked:r.checked,countedUnits:r.countedUnits,wallMs:r.wallMs}))
writeFileSync(join(dir,'summary.json'),JSON.stringify({controlRuns:1,summary},null,2)+'\n');console.log(JSON.stringify(summary,null,2))
