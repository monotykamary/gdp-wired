import {expect,test} from 'bun:test'
import {mkdtempSync,mkdirSync,rmSync,readFileSync,writeFileSync,existsSync,renameSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {fileURLToPath} from 'node:url'
import {phaseMarker} from '../section51-supplier-timed/phase-marker.ts'
const script=fileURLToPath(new URL('../section51-supplier-timed/memory-sampler.sh',import.meta.url))
const stat=(tick:string)=>{const fields=Array<string>(20).fill('0');fields[0]='S';fields[19]=tick;return '42 (name with ) spaces) '+fields.join(' ')+'\n'}
async function sampled(kind:'stop'|'reuse'|'gone'|'foreign-phase'){
 const dir=mkdtempSync(join(tmpdir(),'closing-rss-test-')),out=join(dir,'out'),proc=join(dir,'proc'),stop=join(dir,'stop')
 mkdirSync(out);mkdirSync(join(proc,'42'),{recursive:true});writeFileSync(join(proc,'42','stat'),stat('777'))
 writeFileSync(join(proc,'42','status'),'VmRSS:\t100 kB\nVmHWM:\t240 kB\nVmSize:\t900 kB\n');writeFileSync(join(proc,'uptime'),'12.34 0\n')
 writeFileSync(join(out,'phase-marker.tsv'),`${kind==='foreign-phase'?99:42}\t1\tclosing\t123456\n`)
 const child=Bun.spawn(['bash',script,'42',out,stop,proc,'0.01','777'],{stdout:'ignore',stderr:'pipe'}),exited=child.exited
 let done=false;void exited.then(()=>{done=true},()=>{})
 const timer=setTimeout(()=>{if(!done)process.kill(child.pid,'SIGTERM')},5000)
 try{
  let first=false
  for(let i=0;i<150;i++){if(existsSync(join(out,'memory-samples.jsonl'))&&readFileSync(join(out,'memory-samples.jsonl'),'utf8').includes('\n')){first=true;break}await Bun.sleep(10)}
  expect(first).toBe(true)
  if(kind==='reuse'){writeFileSync(join(proc,'42','stat.next'),stat('999'));renameSync(join(proc,'42','stat.next'),join(proc,'42','stat'))}
  else if(kind==='gone')rmSync(join(proc,'42'),{recursive:true})
  else writeFileSync(stop,'stop')
  expect(await exited).toBe(0)
  const summary=JSON.parse(readFileSync(join(out,'peak-memory.json'),'utf8'))
  const rows=readFileSync(join(out,'memory-samples.jsonl'),'utf8').trim().split('\n').map(row=>JSON.parse(row))
  expect(summary.sampledPeakRssKiB).toBe(100);expect(summary.sampledPeakVmHwmKiB).toBe(240);expect(summary.finalProcessPeakExact).toBe(false)
  expect(rows.every(row=>row.driverStartTicks==='777')).toBe(true)
  expect(rows[0].phase).toBe(kind==='foreign-phase'?'unavailable':'closing')
  expect(summary.stopReason).toBe(kind==='reuse'?'pid-identity-changed':kind==='gone'?'driver-gone':'worker-requested-stop')
  expect(summary.complete).toBe(kind!=='reuse')
 }finally{clearTimeout(timer);if(!done)process.kill(child.pid,'SIGTERM');await exited;rmSync(dir,{recursive:true,force:true})}
}
for(const kind of ['stop','reuse','gone','foreign-phase'] as const)test('external RSS sampler: '+kind,()=>sampled(kind))
test('sampler records an unavailable driver without inventing zero RSS',()=>{
 const dir=mkdtempSync(join(tmpdir(),'closing-rss-unavailable-')),out=join(dir,'out')
 mkdirSync(out)
 try{const run=Bun.spawnSync(['bash',script,'42',out,join(dir,'stop'),join(dir,'absent-proc'),'0.01','777'])
  expect(run.exitCode).toBe(0)
  const summary=JSON.parse(readFileSync(join(out,'peak-memory.json'),'utf8'))
  expect(summary.sampleCount).toBe(0);expect(summary.sampledPeakRssKiB).toBeNull();expect(summary.complete).toBe(false)
  expect(summary.stopReason).toBe('driver-unavailable-before-first-sample')
 }finally{rmSync(dir,{recursive:true,force:true})}
})
test('sampler rejects PID reuse before its very first sample',()=>{
 const dir=mkdtempSync(join(tmpdir(),'closing-rss-first-reuse-')),out=join(dir,'out'),proc=join(dir,'proc')
 mkdirSync(out);mkdirSync(join(proc,'42'),{recursive:true});writeFileSync(join(proc,'42','stat'),stat('999'))
 try{
  const run=Bun.spawnSync(['bash',script,'42',out,join(dir,'stop'),proc,'0.01','777'])
  expect(run.exitCode).toBe(0)
  const summary=JSON.parse(readFileSync(join(out,'peak-memory.json'),'utf8'))
  expect(summary.sampleCount).toBe(0);expect(summary.sampledPeakVmHwmKiB).toBeNull();expect(summary.complete).toBe(false)
  expect(summary.driverStartTicks).toBe('777');expect(summary.stopReason).toBe('pid-identity-changed-before-first-sample')
 }finally{rmSync(dir,{recursive:true,force:true})}
})
test('phase marker is atomic, bounded, and records failures without throwing',()=>{
 const dir=mkdtempSync(join(tmpdir(),'closing-phase-test-'))
 try{const path=join(dir,'phase.tsv'),marker=phaseMarker(path,42);expect(marker.mark('closing-capture')).toBe(true);expect(marker.mark('bad\nphase')).toBe(false)
  expect(readFileSync(path,'utf8')).toMatch(/^42\t1\tclosing-capture\t[0-9]+\n$/);expect(marker.failures).toBe(1)
  const missing=phaseMarker(join(dir,'missing','phase.tsv'),42);expect(missing.mark('closing')).toBe(false);expect(missing.failures).toBe(1)
 }finally{rmSync(dir,{recursive:true,force:true})}
})
