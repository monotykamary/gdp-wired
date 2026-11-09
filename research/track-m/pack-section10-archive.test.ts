import {test,expect} from 'bun:test'
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {brotliDecompressSync} from 'node:zlib'
test('archive packing retains one nested result directory with disambiguated names',()=>{
 const root=mkdtempSync(join(tmpdir(),'section13-pack-test-'));let receipt:string|undefined
 try{
  const child=join(root,'shard');mkdirSync(child);writeFileSync(join(root,'result.json'),'outer');writeFileSync(join(child,'result.json'),'inner')
  const run=Bun.spawnSync([process.execPath,'research/track-m/pack-section10-archive.ts',join(root,'result.json'),child],{stdout:'pipe',stderr:'pipe'});expect(run.exitCode).toBe(0)
  const m=JSON.parse(run.stdout.toString());receipt=m.dir;const bytes=Buffer.from(Array.from({length:m.parts},(_,i)=>readFileSync(join(m.dir,i+'.txt'),'utf8')).join(''),'base64')
  expect(createHash('sha256').update(bytes).digest('hex')).toBe(m.sha256);expect(JSON.parse(brotliDecompressSync(bytes).toString())).toEqual({'result.json':'outer','shard-result.json':'inner'})
 }finally{rmSync(root,{recursive:true,force:true});if(receipt)rmSync(receipt,{recursive:true,force:true})}
})
