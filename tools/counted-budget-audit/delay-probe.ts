// Fresh-process scheduling control: the proof and kernel are unchanged.
import {tripwireGate} from '../../core/clock-tripwire-preload.ts'
import {strict as assert} from 'node:assert'
import {accounts, accountsLaw} from '../../examples/infer.ts'
import {area, areaLaws} from '../../examples/discover.ts'
import {nat, proveRule, proveSteps, rule} from '../../core/dsl.ts'
import {inferLaws} from '../../core/infer.ts'
import {discover} from '../../core/discover.ts'
import {costs} from '../../core/solver.ts'
import {fullWork} from '../../kernel/prove.ts'
const delay=Number(Bun.env.BUDGET_TEST_DELAY ?? 0)
const pause=()=>{if(delay)Atomics.wait(new Int32Array(new SharedArrayBuffer(4)),0,0,delay)}
const mode=Bun.argv[2]
let out: unknown
// Constructing a recurrence proves its stated equations; that is setup, outside
// this discovery request and its clock tripwire.
const prepared=mode==='discover'?area():undefined
const before=fullWork(),raw={...costs}
tripwireGate.active=true
try {
 if(mode==='infer') {
  const r=accounts(),law=accountsLaw(r)
  const v=inferLaws(r,[law],[],{work:20_000,progress:pause})
  assert(v.proven&&v.checked&&!v.stats.stopped)
  const {ms: _ms,...stats}=v.stats;void _ms
  out={proven:v.proven,checked:v.checked,found:v.found.map(f=>f.source),stats}
 } else if(mode==='discover') {
  const r=prepared!,v=discover(r,areaLaws(r),[],undefined,{work:1_000_000})
  assert(v.verdict.proven&&v.verdict.checked)
  out={proven:v.verdict.proven,checked:v.verdict.checked,found:v.found}
 } else {
  const r=rule('delay control').inputs({n:nat}).state({x:0}).step(({n})=>({x:n}))
  const original=r.withSumsOf.bind(r)
  r.withSumsOf=(...args)=>{pause();return original(...args)}
  const law=r.law('nonnegative',({x})=>x.atLeast(0))
  const v=mode==='steps'?proveSteps(r,[law],[],{search:{work:20_000}}):proveRule(r,[law],{search:{work:20_000}})
  assert(v.proven&&v.checked)
  out={proven:v.proven,checked:v.checked,termination:v.termination}
 }
} finally {tripwireGate.active=false}
console.log(JSON.stringify({mode,out,work:fullWork()-before,counters:Object.fromEntries(Object.entries(costs).map(([key,value])=>[key,value-raw[key as keyof typeof costs]]))}))
