import {strict as assert} from 'node:assert'
import {meterKeys, validatePhaseLedger, calibrationRows, type Raw, type Phase} from './contract.ts'
const raw = (n: number): Raw => Object.fromEntries(meterKeys.map(k => [k, n])) as Raw
const phase = (id: number, parentId: number | null, n: number, exclusive: number, depth: number): Phase => ({id,parentId,name: parentId === null ? 'root' : 'strategy.compose',depth,completed:true,raw:raw(n),exclusiveRaw:raw(exclusive),wallMs:n,exclusiveWallMs:exclusive,units:n,exclusiveUnits:exclusive,unitModel:'legacy'})
const events = [phase(2,1,3,3,1), phase(1,null,10,7,0)]
assert(validatePhaseLedger(raw(10), events).exclusiveReconciled)
assert.deepEqual(calibrationRows(raw(10), events).map(r => r.raw.epr), [3,7])
const broken = [
  [events[0]!, {...events[1]!, raw:raw(11)}],
  [events[0]!, {...events[1]!, exclusiveRaw:raw(10)}],
  [events[0]!, {...events[1]!, id:2}],
  [{...events[0]!, parentId:99}, events[1]!],
  [{...events[0]!, depth:3}, events[1]!],
  [...events].reverse(),
  [events[0]!, {...events[1]!, exclusiveWallMs:-1}],
  [events[0]!, {...events[1]!, exclusiveUnits:Infinity}],
  [events[0]!, {...events[1]!, exclusiveRaw:{...raw(7),epr:-1}}],
]
for (const value of broken) assert.throws(() => validatePhaseLedger(raw(10), value))
assert.throws(() => validatePhaseLedger({...raw(10), extra:0} as Raw, events))
assert.throws(() => validatePhaseLedger(raw(10), []))
assert.equal(validatePhaseLedger(raw(10), [events[0]!, {...events[1]!,completed:false}]).rootCompleted, false)
console.log('CALIBRATION_CONTRACT_FIXTURES '+JSON.stringify({passed:true,positive:2,negative:11,keys:meterKeys.length,includesStrategyCompose:true,includesEpr:true}))
