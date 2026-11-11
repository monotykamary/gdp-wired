import {strict as a} from 'node:assert'
import {join} from 'node:path'
import {readFileSync} from 'node:fs'
import {cpus} from 'node:os'
const [root,tag,nText]=process.argv.slice(2),n=Number(nText??200000)
const {compileC}=await import(join(root!,'core/machine.ts'))
const {withBudget}=await import(join(root!,'kernel/prove.ts'))
const {withReachabilityWork}=await import(join(root!,'core/work-observe.ts'))
const {rawWork,fullWork}=await import(join(root!,'core/work-meter.ts'))
const {runtimeWall}=await import(join(root!,'core/runtime-wall.ts'))
const m={name:'admission micro',params:[],inputs:[],state:{x:{op:'const',value:0}},step:{state:{}}}
const x={op:'var',name:'x'},one={op:'const',value:1},eight={op:'const',value:8}
const test=compileC({op:'and',xs:[{op:'<',a:x,b:eight},{op:'<=',a:{op:'add',a:x,b:one},b:eight}]},m)
const st={scalars:{x:0},maps:{}},env={x:0}
const loop=(times:number)=>{let checksum=0;withBudget(1e12,()=>withReachabilityWork(()=>{for(let i=0;i<times;i++){env.x=i&7;checksum+=Number(test(env,st))}}));return checksum}
let calls=0;const admit=runtimeWall.admit
runtimeWall.admit=(units:number,phase:string)=>{calls++;admit?.(units,phase)}
const a0=rawWork();loop(16);const expected=rawWork().reachEvals-a0.reachEvals;runtimeWall.admit=admit
a.equal(calls,expected,'must still admit every expression node')
loop(20000)
const r0=rawWork(),u0=fullWork(),t=performance.now(),checksum=loop(n),wallMs=performance.now()-t,r1=rawWork()
const raw=Object.fromEntries(Object.keys(r1).map(k=>[k,r1[k]-r0[k]]))
console.log('ADMISSION_MEASURE '+JSON.stringify({tag,n,checksum,units:fullWork()-u0,wallMs,raw,admissionCallsPerNode:calls/expected,models:[...new Set(cpus().map(c=>c.model))],bootId:readFileSync('/proc/sys/kernel/random/boot_id','utf8').trim()}))
