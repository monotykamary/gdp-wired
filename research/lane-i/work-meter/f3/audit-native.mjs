import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const [log,baseline]=process.argv.slice(2);assert(log&&baseline)
const text=readFileSync(log,'utf8'),base=readFileSync(baseline,'utf8')
const rows=(text,tag)=>text.split('\n').filter(line=>line.startsWith(tag+' ')).map(line=>JSON.parse(line.slice(tag.length+1)))
const exactly=(text,tag)=>{const found=rows(text,tag);assert.equal(found.length,1,tag);return found[0]}
const source=exactly(text,'F3_NATIVE_SOURCE'),result=exactly(text,'F3_NATIVE_SOLVER_RESULT'),comparison=exactly(text,'F3_NATIVE_COMPARISON'),processReceipt=exactly(text,'F3_NATIVE_PROCESS')
assert.equal(source.config.pin,'32a59b2a4cb38e60ee14cd54a2533bfee76bce89');assert.equal(source.config.baselineSha256,createHash('sha256').update(base).digest('hex'))
assert.equal(processReceipt.exit,0);assert.equal(processReceipt.signal,null);assert.equal(comparison.passed,true)
const off=rows(base,'F3_SOLVER_RESULT').find(row=>row.monitor===false);assert(off)
assert.equal(result.runtime,off.runtime);assert.deepEqual(result.raw,off.raw);assert.deepEqual(result.result,off.result)
assert.deepEqual(Object.keys(result.phases).sort(),Object.keys(off.phases).sort());for(const name of Object.keys(off.phases))assert.deepEqual(result.phases[name].raw,off.phases[name].raw)
const stable=rows(text,'F3_NATIVE_RAW_SILENCE'),changed=rows(text,'F3_NATIVE_WINDOW_CHANGED'),windows=[...stable,...changed]
assert(windows.length<=16);assert.equal(new Set(windows.map(row=>row.reports)).size,windows.length)
for(const row of stable){assert(row.stable&&row.whileRunning);assert.equal(row.heartbeatBefore,row.heartbeatAfter)}
for(const row of changed)assert(!row.stable&&(!row.whileRunning||row.heartbeatBefore!==row.heartbeatAfter))
const attributed=windows.filter(row=>row.native.attributed)
for(const row of attributed){
 assert(row.stable&&row.profileWindow.valid&&row.native.profileWindow.valid);assert(row.native.quietMs>250&&row.native.profileWindow.samplesInWindow>0)
 const a=row.native.before,b=row.native.after;assert(a.valid&&b.valid&&!a.overflow&&!b.overflow&&a.id>0)
 for(const key of ['id','sequence','count','depth'])assert.equal(a[key],b[key])
 assert(source.instrumentation.mapping.some(item=>item.id===a.id))
}
assert.equal(comparison.stableWindows,stable.length);assert.equal(comparison.attributedWindows,attributed.length)
assert.equal(comparison.spanOverflow,result.spanOverflow);assert.equal(comparison.spanCount,result.spanCount)
console.log('F3_NATIVE_AUDIT '+JSON.stringify({passed:true,source:source.config.pin,sameRawAndVerdict:true,stableWindows:stable.length,timestampValidStableWindows:stable.filter(row=>row.profileWindow.valid).length,changedWindows:changed.length,attributedWindows:attributed.length,spanCount:result.spanCount,spanOverflow:result.spanOverflow,operations:attributed.map(row=>source.instrumentation.mapping.find(item=>item.id===row.native.before.id)),scope:'audit of bounded invocation attribution; not exact native instructions, full F3 or W'}))
