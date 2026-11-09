// Delete expanded copies only after verifying their complete retained archive.
import {readdirSync,readFileSync,existsSync,unlinkSync,statSync} from 'node:fs'
import {join,basename} from 'node:path'
import {createHash} from 'node:crypto'
const root=process.argv[2];if(!root)throw new Error('ROOT required')
for(const name of readdirSync(root)){
 const dir=join(root,name),manifest=join(dir,'archive-manifest.json'),archive=join(dir,'receipts.br');if(!existsSync(manifest)||!existsSync(archive))continue
 const m=JSON.parse(readFileSync(manifest,'utf8'));if(createHash('sha256').update(readFileSync(archive)).digest('hex')!==m.sha256)throw new Error('archive hash mismatch: '+name)
 let bytes=0;for(const file of m.files){if(file!==basename(file))throw new Error('unsafe receipt name');if(['actions.jsonl','heartbeat.json'].includes(file))continue;const path=join(dir,file);if(existsSync(path)){bytes+=statSync(path).size;unlinkSync(path)}}
 console.log(JSON.stringify({job:name,retained:archive,verified:true,expandedBytesRemoved:bytes}))
}
