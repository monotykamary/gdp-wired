// Restore a frozen actual-E-14 counted STEP, with its column registry intact.
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const [dir,tag,out]=process.argv.slice(2)
const files:string[]=[]
function walk(p:string){for(const d of readdirSync(p,{withFileTypes:true})){const f=join(p,d.name);if(d.isDirectory())walk(f);else if(d.name==='capture.json.gz')files.push(f)}}
walk(dir!)
if(files.length!==1)throw Error('expected one retained capture')
const p=JSON.parse(gunzipSync(readFileSync(files[0]!)).toString()),c=p.captures.findLast((c:any)=>c.pass===1&&c.base&&c.cert&&c.base.name.endsWith('@step'))
if(!c||!p.record.generatorOnly||p.record.suppliedLaws.length)throw Error('expected an actual generated family STEP packet')
const packet={lawName:c.law,m:p.m,laws:c.laws??p.laws,at:c.at,cert:c.cert,packet:{goal:c.base,decls:c.decls},columns:p.columns,context:{},options:{deferCheck:true}}
mkdirSync(out!,{recursive:true});const text=JSON.stringify(packet);writeFileSync(join(out!,tag+'.packet.json'),text)
console.log(JSON.stringify({frozen:true,tag,source:files[0],sourceHash:createHash('sha256').update(readFileSync(files[0]!)).digest('hex'),packetHash:createHash('sha256').update(text).digest('hex'),law:c.law,pass:c.pass,reads:c.cert.reads.length,instances:c.cert.insts.length}))
