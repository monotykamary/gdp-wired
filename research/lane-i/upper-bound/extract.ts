// Small local receipt extraction and roster construction; no proof work.
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
const [log,out]=process.argv.slice(2);if(!log||!out)throw Error('LOG OUTPUT required')
const lines=readFileSync(log,'utf8').split('\n').filter(l=>l.startsWith('UPPER_FAMILY '));if(lines.length!==1)throw Error(`family receipts ${lines.length}`)
const row=JSON.parse(lines[0]!.slice(13)),bytes=brotliDecompressSync(Buffer.from(row.data,'base64')),sha=createHash('sha256').update(bytes).digest('hex');if(sha!==row.sha256)throw Error('family hash mismatch')
const p=JSON.parse(bytes.toString());if(p.laws.length!==34||p.suppliedLaws.length)throw Error('wrong family')
mkdirSync(out,{recursive:true});writeFileSync(`${out}/family.json`,bytes)
const paths:string[]=[];function walk(dir:string){for(const e of readdirSync(dir,{withFileTypes:true})){const path=`${dir}/${e.name}`;if(e.isDirectory())walk(path);else if(e.name.endsWith('.ts')&&!e.name.endsWith('.test.ts'))paths.push(path)}}walk('core');walk('kernel');paths.sort((a,b)=>a.localeCompare(b))
writeFileSync(`${out}/source.sha256`,paths.map(path=>`${createHash('sha256').update(readFileSync(path)).digest('hex')}  ${path}`).join('\n')+'\n')
const byInput=new Map<string,Set<number>>();const visit=(x:any):void=>{if(!x||typeof x!=='object')return;if(x.op==='='){for(const [a,b]of [[x.a,x.b],[x.b,x.a]])if(a?.op==='var'&&p.m.inputs.includes(a.name)&&b?.op==='const'){const vs=byInput.get(a.name)??new Set<number>();vs.add(b.value);byInput.set(a.name,vs)}}for(const v of Object.values(x))if(v&&typeof v==='object')Array.isArray(v)?v.forEach(visit):visit(v)};visit(p.m.step);visit(p.m.assume)
const selected=[...byInput].filter(([,vs])=>vs.size>2&&vs.size<=16).sort((a,b)=>b[1].size-a[1].size)[0];if(!selected)throw Error('no finite dispatch');const ops=[...selected[1]].sort((a,b)=>a-b);if(ops.length<3||ops.length>16)throw Error('bad operation roster')
const jobs=[];for(const tag of ['star','half','rows','p1','safety'])for(const op of ops)for(const pass of [0,1])for(const ceilings of ['on','off'])jobs.push({name:`${tag}-op${op}-p${pass}-${ceilings}`,cmd:`bash research/lane-i/upper-bound/shard.sh ${tag} ${op} ${pass} ${ceilings}`,cpu:2,memory:14336,timeout:1950})
writeFileSync('research/lane-i/upper-bound/jobs.json',JSON.stringify(jobs,null,2)+'\n')
writeFileSync('research/lane-i/upper-bound/smoke.jobs.json',JSON.stringify(['on','off'].map(ceilings=>({name:`smoke-${ceilings}`,cmd:`bash research/lane-i/upper-bound/shard.sh star ${ops[0]} 1 ${ceilings} 2000`,cpu:2,memory:14336,timeout:90})),null,2)+'\n')
console.log(JSON.stringify({sourceSha:p.sourceSha,familySha256:sha,laws:p.laws.length,targets:p.targets,ops,shards:jobs.length}))
