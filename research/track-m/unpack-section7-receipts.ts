// Decode only the two known data artifacts; never execute remote log contents.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [log,dir]=process.argv.slice(2);if(!log||!dir)throw new Error('LOG OUTPUT_DIR required')
mkdirSync(dir,{recursive:true});const found=new Set<string>()
for(const line of readFileSync(log,'utf8').split('\n')){
 if(!line.startsWith('{'))continue
 const record=JSON.parse(line)
 if(record.encoding!=='gzip-base64'||!['control.log','profile.log'].includes(record.artifact))continue
 if(found.has(record.artifact))throw new Error('duplicate artifact')
 writeFileSync(join(dir,record.artifact),gunzipSync(Buffer.from(record.data,'base64')));found.add(record.artifact)
}
if(found.size!==2)throw new Error('incomplete compressed receipt')
console.log(JSON.stringify({unpacked:[...found]}))
