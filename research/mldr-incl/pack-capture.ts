import {readFileSync,readdirSync} from 'node:fs'
import {brotliCompressSync,constants} from 'node:zlib'
import {createHash} from 'node:crypto'
const dir=process.argv[2]!,limit=Number(process.argv[3]??240000);if(!Number.isInteger(limit)||limit<32768||limit>240000)throw Error('invalid capture limit')
const entries=readdirSync(dir).filter(n=>n.endsWith('.json')||n==='queries.jsonl').map(name=>({name,text:readFileSync(`${dir}/${name}`,'utf8')})),kept=new Map<string,string>(),groups=new Map<string,typeof entries>()
for(const e of entries){if(e.name==='queries.jsonl'||e.name.includes('family')){kept.set(e.name,e.text);continue}const d=JSON.parse(e.text),name=d.law??d.goal?.name??d.goal??'query',key=JSON.stringify([name,d.pass,d.phase,d.outcome]);const group=groups.get(key)??[];group.push(e);groups.set(key,group)}
const sorted=[...groups.entries()].sort(([a],[b])=>Number(!a.includes('one primary'))-Number(!b.includes('one primary'))||a.localeCompare(b))
for(const [,group]of sorted){group.sort((a,b)=>Number(a.name.match(/-(\d+)\.json$/)?.[1]??0)-Number(b.name.match(/-(\d+)\.json$/)?.[1]??0));for(const e of [...group.slice(0,2),...group.slice(-4)])kept.set(e.name,e.text)}
const encode=()=>brotliCompressSync(Buffer.from(JSON.stringify(Object.fromEntries(kept))),{params:{[constants.BROTLI_PARAM_QUALITY]:4}})
let bytes=encode();while(bytes.length>limit&&kept.size>3){const keys=[...kept.keys()].filter(n=>n!=='queries.jsonl'&&!n.includes('family'));for(const key of keys.slice(-Math.max(1,Math.ceil(keys.length/4))))kept.delete(key);bytes=encode()}
if(bytes.length>(process.argv[3]?limit:260000))throw Error('capture headers exceed log allowance')
console.log(JSON.stringify({artifact:'mldr-incl-capture',files:kept.size,omitted:entries.length-kept.size,sha256:createHash('sha256').update(bytes).digest('hex'),data:bytes.toString('base64')}))
