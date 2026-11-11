import {strict as assert} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {readProfileArchive} from './profile-archive.ts'
const {selectProfileWindow}=await import('./profile-window.mjs')
const parse=(lines:string[],tag:string)=>lines.filter(l=>l.startsWith(tag+' ')).map(l=>JSON.parse(l.slice(tag.length+1)))
const reports=[]
for(const mode of ['silent','zero-price','priced']){
 const lines=readFileSync(join(process.argv[2]!,mode+'.log'),'utf8').split('\n'),archives=parse(lines,'F3_UNIT_PROFILE'),windows=parse(lines,'F3_UNIT_SILENCE'),summary=parse(lines,'F3_UNIT_OBSERVER_SUMMARY'),result=parse(lines,'F3_UNIT_CONTROL')
 assert.equal(parse(lines,'F3_UNIT_ERROR').length,0);assert.equal(summary.length,1);assert(!summary[0].coverageCapped);assert(summary[0].maxTickGapMs<250);assert.equal(result.length,1);assert(result[0].snapshot.valid)
 const verified=windows.filter(window=>{
  const record=archives.find(a=>a.sha256===window.profileSha256);assert(record,'every capture needs complete raw profile')
  const profile=readProfileArchive(record),selected=selectProfileWindow(profile,window.unitSilentMs)
  assert.deepEqual(selected.timing,window.profileWindow);assert.deepEqual(selected.stack,window.stack)
  assert(window.unitSilentMs>250&&window.unitsBefore===window.unitsAfter&&window.stable)
  return window.profileWindow.valid&&window.stack.some((f:any)=>f.functionName==='mainThreadUnitControl')
 })
 if(mode==='priced'){assert.equal(windows.length,0);assert(result[0].snapshot.units>0)}
 else{if(!verified.length){console.log('F3_UNIT_CONTROL_FAILURE '+JSON.stringify({mode,summary,windows:windows.map(w=>({unitSilentMs:w.unitSilentMs,profileWindow:w.profileWindow,stack:w.stack.map((f:any)=>f.functionName)})),result}));for(const archive of archives)console.log('F3_UNIT_RETAINED_PROFILE '+JSON.stringify(archive))};assert(verified.length>0,'timestamp-valid main-thread silent capture');assert.equal(result[0].snapshot.units,0)}
 if(mode==='zero-price')assert(result[0].snapshot.raw.tableCells>0)
 if(verified.length){const window=verified[0];console.log('F3_UNIT_EVIDENCE '+JSON.stringify({mode,window,profile:archives.find(a=>a.sha256===window.profileSha256)}))}
 reports.push({mode,stableWindows:windows.length,verifiedWindows:verified.length,archives:archives.length,maxTickGapMs:summary[0].maxTickGapMs})
}
console.log('F3_UNIT_CONTROLS '+JSON.stringify({passed:true,reports,scope:'Node synthetic unit-observer capability; not original-model, Bun or reference-host F3'}))
