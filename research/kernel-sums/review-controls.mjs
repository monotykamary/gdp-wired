import assert from 'node:assert/strict'
import {raftTally} from '../realworld/items/dist-etcd-raft.ts'
import {proveRule,when} from '../../core/dsl.ts'
import {searchAggregate} from '../../core/aggregate-search.ts'
import {proofOutput} from '../../core/proof-output.ts'
assert.equal(process.version,'v24.22.1')
const r=raftTally(), source=r.machine
const aggregate=r.law('tally bounded',({yes,no,n})=>yes.plus(no).atMost(n))
const omitted=r.law('false kind-like obligation',({yes})=>yes.eq(1))
assert(searchAggregate(source,aggregate,()=>r.kindLaws(),6000)?.kinds,'failed positive control')
assert(!searchAggregate(source,aggregate,()=>[omitted],6000),'aggregate accepted despite a false companion obligation')
const auto=r.law('tally with an implicit sum',({yes,V})=>yes.atLeast(0).and(V.sum(v=>when(v.is('yes'),1,0)).atLeast(0)))
assert.notEqual(r.withSumsOf(auto),r,'no automatically materialized sum')
assert.equal(searchAggregate(source,auto,()=>r.kindLaws(),6000),undefined,'pre-elaboration snapshot must be declined')
let event
proofOutput.on=e=>{event=e}
const verdict=proveRule(r,[auto],{search:{ms:5000}})
assert.equal(typeof verdict.proven,'boolean')
const usesAggregate=n=>n?.kind==='aggregate'||n?.kind==='derived'&&n.parents.some(usesAggregate)
assert(!usesAggregate(event?.proof),'implicit sum proof did not fall back to ordinary solver')
console.log(JSON.stringify({controls:['actual-kind-family','false-kind','implicit-sum-fallback'],verdict:{proven:verdict.proven,checked:verdict.checked}}))
