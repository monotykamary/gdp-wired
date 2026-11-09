import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {checkCountedLaws,countedObligations,checkMC} from '../../kernel/kernel.ts'
const version=process.argv[2]??'v1',dir='/tmp/paxos-law12-alpha-'+version+'/';mkdirSync(dir,{recursive:true})
const sha=(x:string)=>createHash('sha256').update(x).digest('hex')
const log=readFileSync('evidence/capture-paxos_epr.log','utf8'),b64=log.match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)![1]!
writeFileSync(dir+'archive.tar.xz',Buffer.from(b64,'base64'));const t=spawnSync('tar',['-xJf',dir+'archive.tar.xz','-C',dir]);if(t.status!==0)throw Error(String(t.stderr))
const files=readdirSync(dir),packet=files.find(x=>x.endsWith('.json')&&!x.endsWith('.result.json'))!,lf=files.find(x=>x.endsWith('.lean'))!,raw=readFileSync(dir+packet,'utf8'),lean=readFileSync(dir+lf,'utf8')
if(sha(raw)!=='dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386'||sha(lean)!=='e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1')throw Error('hash mismatch')
const x=JSON.parse(raw,(_k,v)=>v?.__map?new Map(v.__map):v?.__set?new Set(v.__set):v),c=x.counted
console.log('ORIGINAL_PACKET_SHA',sha(raw),'ORIGINAL_LEAN_SHA',sha(lean));console.log('TS_ORIGINAL_ACCEPTS',checkCountedLaws(c.machine,c.laws,c.proof))
const old=JSON.stringify(c.machine.step.flags.rowOk),q=c.machine.step.flags.rowOk
if(q.op!=='all'||q.key!=='k$21'||q.keys?.length)throw Error('wrong binder')
const fresh='paxosLaw12AlphaFresh';if(raw.includes(fresh))throw Error('not fresh')
let occurrences=0
function rename(t:any):any {if(!t||typeof t!=='object')return t;if(Array.isArray(t))return t.map(rename);if(t.op==='all')throw Error('nested binder: refuse blind rename');if(t.op==='var'&&t.name==='k$21'){occurrences++;return {...t,name:fresh}}return Object.fromEntries(Object.entries(t).map(([k,v])=>[k,rename(v)]))}
c.machine.step.flags.rowOk={...q,key:fresh,c:rename(q.c)}
const changed=JSON.stringify(c.machine.step.flags.rowOk);console.log('ALPHA_JSON_DELTA',JSON.stringify({old:JSON.parse(old),new:JSON.parse(changed),occurrences}))
const alphaRaw=JSON.stringify(x,(_k,v)=>v instanceof Map?{__map:[...v]}:v instanceof Set?{__set:[...v]}:v)
writeFileSync(dir+'alpha.packet.json',alphaRaw);console.log('ALPHA_PACKET_SHA',sha(alphaRaw))
console.log('TS_ALPHA_ACCEPTS',checkCountedLaws(c.machine,c.laws,c.proof))
for(const o of countedObligations(c.machine,c.laws,c.proof.instances))if(o.goal.name===c.laws[12].name+' @start'||o.goal.name===c.laws[12].name+' @step')console.log('TS_ALPHA_LAW12',o.goal.name,checkMC(o.goal.hyps,o.decls,c.proof.certs[o.goal.name]))
const header=lean.split('theorem verified_check :')[0]!,machine=header.slice(header.indexOf('def verified_machine'),header.indexOf('def verified_decls'))
const start=machine.indexOf('(72, [29],');if(start<0)throw Error('missing tuple');let depth=0,end=-1
for(let i=start;i<machine.length;i++){if(machine[i]==='(')depth++;if(machine[i]===')'&&--depth===0){end=i+1;break}}
if(end<0)throw Error('unclosed tuple');const tuple=machine.slice(start,end),newTuple=tuple.replace('[29]','[131]').replaceAll('.var 29)', '.var 131)')
if((tuple.match(/\.var 29\)/g)??[]).length!==occurrences)throw Error('bound occurrence count mismatch')
const alphaMachine=(machine.slice(0,start)+newTuple+machine.slice(end)).replace('def verified_machine','def paxos_alpha_machine')
const template=readFileSync('research/verify-all/paxos-law12-alpha-'+version+'.lean','utf8'),out=header+alphaMachine+template
writeFileSync(dir+'alpha-check.lean',out);console.log('ALPHA_LEAN_SHA',sha(out),'TEMPLATE_SHA',sha(template));console.log('LEAN_BINDER_DELTA',tuple,'=>',newTuple)
console.log('GENERATED_LEAN',dir+'alpha-check.lean')
