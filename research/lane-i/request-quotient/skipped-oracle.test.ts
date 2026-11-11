import {expect,test} from 'bun:test'
import {BudgetExpired} from '../../../kernel/prove.ts'
import {SkippedRequestOracle,UnexpectedSkippedOutcome} from './skipped-oracle.ts'
const site={file:'core/machine.ts',sha256:'03d69e7e9e768a7e6735294f819da90d965f73d72c4134ab9ef74715d36f51bf',line:819,expression:'if (m.assume && !evalC(m.assume, env, st, plain)) throw new RangeError(refused(m))'}
const machine={name:'control',assume:{op:'=',a:{op:'const',value:0},b:{op:'const',value:1}}},state={n:0},next={n:1}
function setup(){const oracle=new SkippedRequestOracle(site,(_m,s)=>JSON.stringify(s));oracle.keep(machine,state,7,next);return oracle}
for(const [label,error]of [
 ['TypeError',new TypeError('injected into step')],
 ['ordinary Error',new Error('injected into step')],
 ['BudgetExpired',new BudgetExpired('injected oracle interruption')],
 ['unexpected RangeError',new RangeError('injected into step')],
 ['forged guard-message RangeError',new RangeError("control: the request fails the rule's assumption, so no proof covers the step it would take")],
] as const)test(label+' is reported and never counted as semantic refusal',()=>{
 const oracle=setup(),step=()=>{throw error}
 expect(()=>oracle.skip(machine,{},state,{},7,step)).toThrow(UnexpectedSkippedOutcome)
 const result=oracle.snapshot();expect(result.unexpected).toBe(1);expect(result.refused).toBe(0)
 expect(result.exceptions[0]?.exceptionClass).toBe(error.constructor.name)
 expect(result.exceptions[0]?.message).toBe(error.message);expect(result.exceptions[0]?.origin).toBeUndefined()
})
test('only the source-bound assumption marker authorizes a guard refusal',()=>{
 const oracle=setup(),step=()=>{throw oracle.assumptionFailure(new RangeError("control: the request fails the rule's assumption, so no proof covers the step it would take"),machine)}
 oracle.skip(machine,{},state,{},7,step)
 const result=oracle.snapshot();expect(result.refused).toBe(1);expect(result.unexpected).toBe(0)
 expect(result.exceptions[0]?.origin).toMatchObject(site);expect(result.exceptions[0]?.origin?.guardSHA256).toHaveLength(64)
})
test('a distinct successor is not swallowed as refusal',()=>{
 const oracle=setup();expect(()=>oracle.skip(machine,{},state,{},7,()=>({n:2}))).toThrow('distinct skipped successor')
 expect(oracle.snapshot().refused).toBe(0);expect(oracle.snapshot().matched).toBe(0)
})
test('a missing class representative fails closed before invoking the step',()=>{
 const oracle=setup();let ran=false
 expect(()=>oracle.skip(machine,{},state,{},8,()=>{ran=true;return next})).toThrow('missing successful class representative')
 expect(ran).toBe(false);expect(oracle.snapshot().refused).toBe(0)
})
test('unmarked non-Error throws fail closed too',()=>{
 const oracle=setup();expect(()=>oracle.skip(machine,{},state,{},7,()=>{throw 'injected string'})).toThrow(UnexpectedSkippedOutcome)
 expect(oracle.snapshot().unexpected).toBe(1);expect(oracle.snapshot().refused).toBe(0)
})
