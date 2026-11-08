// Pure artifact analysis: no prover/search calls.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {instId,keyId} from '../../core/count-support.ts'
import {substE,type CountCert,type Instances} from '../../kernel/kernel.ts'
import {type E} from '../../core/machine.ts'
const text=readFileSync(process.argv[2]!,'utf8'),line=text.split('\n').find(l=>l.startsWith('FAILURES_GZIP '));if(!line)throw Error('no failure packet')
const failures=JSON.parse(gunzipSync(Buffer.from(line.slice('FAILURES_GZIP '.length),'base64')).toString()) as {index:number,first?:any,last?:any}[]
const source=JSON.parse(readFileSync(process.argv[3]!,'utf8')) as {instances:Instances},hand=JSON.parse(readFileSync(process.argv[4]!,'utf8')) as CountCert,fixture=JSON.parse(readFileSync(process.argv[5]!,'utf8'))
const target=Number(process.argv[6]??11),hit=failures.find(f=>f.index===target);if(!hit)throw Error('target has no failure snapshot')
const rows=(at:Instances)=>Object.entries(at).flatMap(([name,values])=>{const law=fixture.laws.find((l:any)=>l.name===name),width=name.startsWith('?')?1:1+(law?.keys?.length??0);return Array.from({length:values.length/width},(_,j)=>({name,tuple:values.slice(j*width,(j+1)*width)}))})
const identity=(r:{name:string,tuple:E[]})=>JSON.stringify([r.name,r.tuple.map(keyId)]),required=rows(source.instances),want=new Set(required.map(identity)),index=(name:string)=>fixture.laws.findIndex((l:any)=>l.name===name)
for(const phase of ['first','last'] as const){
 const pack=hit[phase];if(!pack)continue
 const cert=pack.certificateRequest as CountCert,aliases:Record<string,E>={}
 for(const i of cert.insts){const match=hand.insts.find(h=>instId(h,hand.reads)===instId(i,cert.reads));if(match)aliases[i.wit]={op:'var',name:match.wit}}
 const actual=rows(pack.instances).map(r=>({...r,tuple:r.tuple.map(t=>substE(t,{vars:aliases,maps:{},flags:{}}))})),have=new Set(actual.map(identity)),extras=actual.filter(r=>!want.has(identity(r))),groups:Record<string,number>={}
 for(const r of extras){const key=index(r.name)<0?r.name:String(index(r.name));groups[key]=(groups[key]??0)+1}
 console.log(JSON.stringify({target,phase,event:pack.phase,rawHyps:pack.raw.hyps.length,encodedHyps:pack.hyps?.length,insts:cert.insts.map(i=>({wit:i.wit,id:instId(i,cert.reads)})),missing:required.filter(r=>!have.has(identity(r))).map(r=>({...r,index:index(r.name)})),extraGroups:groups,generation:pack.generation}))
}
