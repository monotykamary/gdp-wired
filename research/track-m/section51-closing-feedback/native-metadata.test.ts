import {expect,test} from 'bun:test'
import {nativeMetadataFixture} from './native-metadata.fixture.ts'
import {isCheckedReducedScope,snapshotCountScopeBinding} from '../../../core/count-proof-scope.ts'
import {withBudget,clock,fullRate} from '../../../kernel/prove.ts'
import {workAmount} from '../../../core/work-amount.ts'
import {completeWorkProfile} from '../../../core/work-profile.ts'
const fullTest=completeWorkProfile.enabled?test:test.skip
fullTest('R1: observing/mutating/freezing detached scope views cannot change the private binding',()=>withBudget(workAmount(25000000n),()=>{
 const f=nativeMetadataFixture(clock()+25000000/fullRate),token=f.scoped.checkedReduced!
 const a=snapshotCountScopeBinding(token)!,b=snapshotCountScopeBinding(token)!
 expect(a).not.toBe(b);expect(a.context).not.toBe(b.context);expect(a.context[0]).not.toBe(b.context[0]);expect(a.laws).not.toBe(b.laws)
 expect(a.token).toBe(token);expect(a.laws.every(law=>f.family.includes(law))).toBe(true)
 const before=JSON.stringify(b.context)
 expect(Reflect.set(a,'scope','forged')).toBe(false)
 expect(Reflect.set(a.context[0]!, 'key','forged')).toBe(false)
 expect(Reflect.set(a.context,0,{name:'forged',key:'forged'})).toBe(false)
 expect(Reflect.set(a.laws,0,{name:'forged'})).toBe(false)
 Object.freeze(a);Object.freeze(a.context);Object.freeze(a.laws)
 expect(JSON.stringify(snapshotCountScopeBinding(token)!.context)).toBe(before)
 expect(snapshotCountScopeBinding(token)!.scope).toBe(b.scope)
 expect(isCheckedReducedScope(f.scoped,f.m,f.family)).toBe(true)
}))
