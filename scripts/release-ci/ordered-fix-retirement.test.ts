import {expect,test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {matchKnownFailure,validateKnownFailuresPolicy} from './known-failures.ts'

const retired=['trading','extract-rb','extract-ex','extract-c','extract-jvm','extract-orm','extract-go','runner-cli-c-jvm']
test('repaired source groups cannot be accepted as known failures again',()=>{
  const jobs=JSON.parse(readFileSync(new URL('../../supercomputer/suite.json',import.meta.url),'utf8'))
  const policy=validateKnownFailuresPolicy(JSON.parse(readFileSync(new URL('./known-failures.json',import.meta.url),'utf8')),jobs)
  for(const job of retired){
    expect(policy.requiredPass).toContain(job)
    expect(policy.entries.some(entry=>entry.job===job)).toBe(false)
    expect(()=>matchKnownFailure(policy,job,'0'.repeat(64),1,{failedTests:['unexpected failure'],diagnostics:[]})).toThrow('required-pass job failed')
  }
  expect(policy.entries.map(entry=>entry.job).sort()).toEqual(['extract-rs','extract-swift','lean-protocols-wo'])
})
