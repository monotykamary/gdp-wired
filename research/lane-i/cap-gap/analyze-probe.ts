import {readFileSync} from 'node:fs'
import {strict as a} from 'node:assert'
const [probe,baseline]=process.argv.slice(2)
const read=(file:string,key:string)=>{const line=readFileSync(file,'utf8').split('\n').find(s=>s.startsWith(key));if(!line)throw Error('missing '+key);return JSON.parse(line.slice(key.length))}
const original=read(baseline!,'CANDIDATE_CASE '),instrumented=read(probe!,'CANDIDATE_CASE '),data=read(probe!,'CAP_GAP_PROBE ')
a.deepEqual(original.raw,instrumented.raw);a.deepEqual(original.result,instrumented.result);a.equal(original.searchUnits,instrumented.searchUnits)
const gap=(g:any)=>({...g,delta:g.from.raw&&Object.fromEntries(Object.keys(g.from.raw).map(k=>[k,g.to.raw[k]-g.from.raw[k]]).filter(([,v])=>v!==0)),samples:g.samples.slice(0,8),sampleSites:g.samples.length})
console.log('CAP_GAP_ANALYSIS '+JSON.stringify({rawAndVerdictIdentical:true,polls:data.polls,rootEnd:data.rootEnd,rootStart:data.rootStart,firstAbove:{...data.firstAbove,gap:gap(data.firstAbove.gap)},largest:data.top.slice(0,4).map(gap)}))
