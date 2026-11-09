import {expect,test} from 'bun:test'
import {profileCheck,readCheckProfile} from './check-cost-profile.ts'
test('check profiler preserves results and separates nested calls',()=>{
 const token={ok:true};expect(profileCheck('parent',()=>profileCheck('child',()=>token))).toBe(token)
 const p=readCheckProfile();expect(p.parent!.calls).toBe(1);expect(p.child!.calls).toBe(1);expect(p.parent!.totalMs).toBeGreaterThanOrEqual(p.parent!.selfMs);expect(p.parent!.totalMs).toBeGreaterThanOrEqual(p.child!.totalMs)
})
test('check profiler rethrows failures and unwinds before the next call',()=>{
 const failure=new Error('kept');expect(()=>profileCheck('failure',()=>{throw failure})).toThrow(failure)
 expect(profileCheck('next',()=>false)).toBe(false);const p=readCheckProfile();expect(p.failure!.calls).toBe(1);expect(p.next!.calls).toBe(1);expect(p.next!.selfMs).toBeGreaterThanOrEqual(0)
})
