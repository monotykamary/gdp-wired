import {expect,test} from 'bun:test'
import {mkdtempSync,mkdirSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'

const root=resolve(import.meta.dir,'../..'),runner=join(root,'scripts/test-shards.ts')
function fixture(run:(dir:string,good:string,bad:string)=>void){
 const dir=mkdtempSync(join(tmpdir(),'lane-i-test-load-'))
 try{
  const good=join(dir,'good.test.ts'),bad=join(dir,'broken.test.ts')
  writeFileSync(join(dir,'exports.mjs'),'export const present=1;\n')
  writeFileSync(good,"import {test,expect} from 'bun:test'; test('good',()=>expect(true).toBe(true));\n")
  writeFileSync(bad,"import {test,expect} from 'bun:test'; import {absent} from './exports.mjs'; test('broken',()=>expect(absent).toBeDefined());\n")
  run(dir,good,bad)
 }finally{rmSync(dir,{recursive:true,force:true})}
}
test('the quick roster explicitly includes the range and member-premise test modules',()=>{
 const r=spawnSync(process.execPath,[runner,'--list'],{cwd:root,encoding:'utf8',timeout:15000})
 expect(r.status).toBe(0)
 for(const path of ['core/count-ranges.test.ts','core/count-write-frames.test.ts','core/count-recovery/member-premises.test.ts','research/lane-i/test-load-propagation.test.ts'])expect(r.stdout).toContain(path)
})
test('one passing file cannot mask an unexported import in a second test file',()=>fixture((_dir,good,bad)=>{
 const r=spawnSync(process.execPath,['test',good,bad],{encoding:'utf8',timeout:15000})
 expect(r.status).not.toBeNull();expect(r.status!).toBeGreaterThan(0)
 expect(r.stderr).toContain('absent')
}))
test('the quick suite propagates a real load failure and stops before the next group',()=>fixture((dir,good,bad)=>{
 const bin=join(dir,'bin');mkdirSync(bin)
 // Only substitute the first test group. The actual suite controls grouping,
 // error propagation and stopping; the real Bun process exercises import failure.
 writeFileSync(join(bin,'bun'),'#!/bin/sh\nif [ "$1" = "test" ]; then exec "$LANE_I_REAL_BUN" test "$LANE_I_GOOD" "$LANE_I_BAD"; fi\nexit 0\n',{mode:0o755})
 const r=spawnSync(process.execPath,[runner],{cwd:root,encoding:'utf8',timeout:15000,env:{...process.env,PATH:bin+':'+(process.env.PATH??''),LANE_I_REAL_BUN:process.execPath,LANE_I_GOOD:good,LANE_I_BAD:bad}})
 expect(r.status).not.toBeNull();expect(r.status!).toBeGreaterThan(0)
 expect(r.stderr).toContain('absent');expect(r.stderr).toContain('(cd core) bun test')
 expect(r.stderr).not.toContain('(cd kernel) bun test')
}))
