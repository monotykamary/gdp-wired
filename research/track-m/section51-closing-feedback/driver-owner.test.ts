import {expect,test} from 'bun:test'
import {mkdtempSync,rmSync,existsSync,readFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {fileURLToPath} from 'node:url'
const fixture=fileURLToPath(new URL('./driver-owner.fixture.sh',import.meta.url)),helper=fileURLToPath(new URL('../section51-supplier-timed/driver-owner.sh',import.meta.url))
for(const mode of ['normal','terminate','ignore'])test('R2 exact child ownership and cleanup: '+mode,async()=>{
 const out=mkdtempSync(join(tmpdir(),'driver-owner-')),worker=Bun.spawn(['bash',fixture,'worker',mode,out,helper],{stdout:'ignore',stderr:'pipe'}),exited=worker.exited
 let done=false;void exited.then(()=>{done=true},()=>{})
 try{
  if(mode!=='normal'){
   for(let i=0;i<300&&!existsSync(join(out,'worker-ready'));i++)await Bun.sleep(10)
   expect(existsSync(join(out,'worker-ready'))).toBe(true);process.kill(worker.pid,'SIGTERM')
  }
  const timeout=setTimeout(()=>{if(!done)process.kill(worker.pid,'SIGKILL')},8000)
  let code:number;try{code=await exited}finally{clearTimeout(timeout)}
  expect(code!).toBe(mode==='normal'?0:143)
  const retirement=JSON.parse(readFileSync(join(out,'retirement.json'),'utf8')),cleanup=JSON.parse(readFileSync(join(out,'cleanup.json'),'utf8'))
  expect(retirement.joined).toBe(true);expect(cleanup.terminalBeforeRemoval).toBe(true);expect(cleanup.scratchRemoved).toBe(true)
  expect(retirement.termSent).toBe(mode!=='normal');expect(retirement.killSent).toBe(mode==='ignore')
  expect(retirement.pid).toBe(Number(readFileSync(join(out,'child-pid.txt'),'utf8')))
 }finally{
  if(!done)process.kill(worker.pid,'SIGKILL');await exited
  const owner=join(out,'owner.identity')
  if(existsSync(owner)){
   const [pid,ticks]=readFileSync(owner,'utf8').trim().split(' '),path=`/proc/${pid}/stat`
   if(existsSync(path))try{const raw=readFileSync(path,'utf8'),fields=raw.slice(raw.lastIndexOf(') ')+2).split(' ');if(fields[19]===ticks&&fields[0]!=='Z')process.kill(Number(pid),'SIGKILL')}catch{}
  }
  rmSync(out,{recursive:true,force:true})
 }
},12000)
