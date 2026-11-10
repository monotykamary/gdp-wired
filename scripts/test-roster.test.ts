import {expect,test} from 'bun:test'
import {mkdirSync,mkdtempSync,rmSync,writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {assertTestRoster,auditTestRoster,coreKernelTests,longSuiteTests} from './test-roster.ts'
test('a newly added core or kernel test must be explicitly scheduled',()=>{
 expect(()=>assertTestRoster(['core/new.test.ts'],[],[])).toThrow('core/new.test.ts')
 expect(()=>assertTestRoster(['kernel/new.test.ts'],[],[])).toThrow('kernel/new.test.ts')
 expect(()=>assertTestRoster(['core/new.test.ts'],['core/new.test.ts'],[])).not.toThrow()
})
test('existing long-suite coverage is explicit and tracked',()=>{
 const long=longSuiteTests([{cwd:'.',cmd:'bun install && cd core && bun test a.test.ts && cd .. && bun test kernel/b.test.ts'}])
 expect(long).toEqual(['core/a.test.ts','kernel/b.test.ts'])
 expect(()=>assertTestRoster(long,[],long)).not.toThrow()
})
test('dynamic shell globs never claim coverage of a new file',()=>{
 const long=longSuiteTests([{cwd:'core',cmd:'bun test *.test.ts'}])
 expect(long).toEqual([])
 expect(auditTestRoster(['core/new.test.ts'],[],long).missing).toEqual(['core/new.test.ts'])
})
test('echoed test commands do not cover files',()=>{
 expect(longSuiteTests([{cwd:'core',cmd:'echo bun test fake.test.ts'}])).toEqual([])
 expect(longSuiteTests([{cwd:'kernel',cmd:'FUZZ_SEED=1 GDP_VERIFY=1 bun test real.test.ts'}])).toEqual(['kernel/real.test.ts'])
})
test('missing, duplicate and nonexistent quick entries are refused',()=>{
 expect(auditTestRoster(['core/a.test.ts'],['core/a.test.ts','core/a.test.ts','core/gone.test.ts'],[])).toEqual({missing:[],nonexistent:['core/gone.test.ts'],duplicates:['core/a.test.ts']})
 expect(()=>assertTestRoster(['core/a.test.ts'],['core/a.test.ts','core/a.test.ts'],[])).toThrow()
})
test('filesystem discovery includes nested core tests and ignores non-tests',()=>{
 const root=mkdtempSync(join(tmpdir(),'test-roster-'))
 try{mkdirSync(join(root,'core/nested'),{recursive:true});mkdirSync(join(root,'kernel'));writeFileSync(join(root,'core/nested/new.test.ts'),'');writeFileSync(join(root,'core/source.ts'),'');writeFileSync(join(root,'kernel/check.test.ts'),'')
 expect(coreKernelTests(root)).toEqual(['core/nested/new.test.ts','kernel/check.test.ts'])
 }finally{rmSync(root,{recursive:true,force:true})}
})
