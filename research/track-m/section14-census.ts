import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {brotliDecompressSync} from 'node:zlib'
const [archive,input,out]=process.argv.slice(2);if(!archive||!input||!out)throw new Error('ARCHIVE PACKET OUT required')
const files=JSON.parse(brotliDecompressSync(readFileSync(archive)).toString()),r=JSON.parse(files['result.json']),p=JSON.parse(readFileSync(input,'utf8'))
const events=r.trace.events.filter((e:any)=>e.kind==='source-result'&&e.outcome==='checked'),indices=[...new Set<number>(events.map((e:any)=>e.index))].sort((a,b)=>a-b),reads=new Map<string,any>(p.cert.reads.map((r:any)=>[r[0],r])),wanted=new Set(['xm','xn','cfgSize','inS','inX'])
const rows=indices.map(index=>{const inst=p.cert.insts[index],rs=inst.terms.map(([k,v]:[number,string])=>({coefficient:k,read:reads.get(v)})),maps=rs.map((r:any)=>r.read?.[1]),phases=new Set(maps.map((m:string)=>m.endsWith('#')?'post':'pre'));return {index,inst,reads:rs,maps,allWanted:maps.every((m:string)=>wanted.has(m.replace(/#$/,''))),phase:phases.size===1?[...phases][0]:'mixed'}})
const groups=Object.fromEntries(['pre','post','mixed'].map(phase=>[phase,rows.filter(r=>r.allWanted&&r.phase===phase).map(r=>r.index)]))
const report={checkedAttempts:events.length,distinctIndices:indices.length,closureSizes:[...new Set(r.trace.frames.filter((f:any)=>f.kind==='closure').map((f:any)=>f.meta.insts))],rootInstances:p.cert.insts.length,groups,rows}
writeFileSync(join(out,'census.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({checkedAttempts:events.length,distinctIndices:indices.length,groups,closureSizes:report.closureSizes}))
