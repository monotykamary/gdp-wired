import assert from 'node:assert/strict'
import {writeFileSync} from 'node:fs'
import {corpus} from '../research/realworld/corpus.ts'
import {proofOutput} from '../core/proof-output.ts'
import {checkFiniteSum} from '../kernel/finite-sum.ts'
import {checkGhostWrite,ghostWriteTheory} from '../kernel/ghost-write.ts'
import {toLean} from '../lean-kernel/emit.ts'
import {checkLaws} from '../kernel/kernel.ts'
import {get,n,same,x} from '../core/machine.ts'
const [item,index,file]=process.argv.slice(2), id=Number(index)
assert.equal(process.version,'v24.22.1')
const selected=corpus.find(x=>x.id===item)?.laws[id]
assert(selected)
function aggregate(node){return node?.kind==='aggregate'?node:node?.kind==='derived'?node.parents.map(aggregate).find(Boolean):undefined}
let captured
proofOutput.on=event=>{captured=event}
const started=performance.now(), result=selected.prove(60000), ms=performance.now()-started
assert(result.proven&&result.checked,JSON.stringify(result))
const p=aggregate(captured?.proof)
assert(p,'default path did not retain native aggregate certificate')
assert.equal(p.law.name,selected.name)
assert.deepEqual(p.machine,captured.original.machine,'checker used a different public source snapshot')
const {machine,law,certificate,kinds}=p
assert(kinds?.laws.length,'lost the source kind obligations')
if(kinds) {
  assert(checkLaws(machine,kinds.laws,kinds.proof))
  const missing=structuredClone(kinds.proof)
  delete missing.trees[Object.keys(missing.trees)[0]]
  assert(!checkLaws(machine,kinds.laws,missing),'missing kind obligation accepted')
}
if(certificate.kind==='finite-sum') {
  assert(checkFiniteSum(machine,law,certificate))
  const missing=structuredClone(certificate)
  delete missing.trees.field0_delta
  assert(!checkFiniteSum(machine,law,missing),'missing per-key balance accepted')
  const outside=structuredClone(machine), {bound,key,fields}=certificate.layout
  let removed=false
  function withoutSupport(c) {
    if(c.op==='and')return {...c,xs:c.xs.map(withoutSupport)}
    if(c.op==='<='&&c.a.op==='var'&&c.a.name===key&&c.b.op==='var'&&c.b.name===bound){removed=true;return same(n(0),n(0))}
    return c
  }
  outside.assume=withoutSupport(outside.assume)
  assert(removed&&!checkFiniteSum(outside,law,certificate),'out-of-support write accepted')
  const stale=structuredClone(machine)
  stale.step.state[fields[0].field]=x(fields[0].field)
  assert(!checkFiniteSum(stale,law,certificate),'stale accumulator accepted')
}
else {
  writeFileSync(`${process.env.SUPERCOMPUTER_OUTPUT_DIR}/certificate.json`,JSON.stringify(p))
  assert(checkGhostWrite(machine,law,certificate),'recheck after proveRule')
  const {recipe:r}=certificate, ghost=r.ghostMap
  const intrude=structuredClone(machine)
  const scalar=Object.keys(intrude.state)[0]
  if(scalar) intrude.step.state[scalar]=get(ghost,n(0))
  else intrude.step.maps[r.group].value=get(ghost,n(0))
  assert(!checkGhostWrite(intrude,law,certificate),'ghost read into original accepted')
  const freeWrite=structuredClone(certificate)
  freeWrite.target.step.maps[ghost].value=n(123)
  assert(!checkGhostWrite(machine,law,freeWrite),'unrelated ghost assignment accepted')
  const stale=structuredClone(certificate)
  const next=stale.target.step.maps[ghost].value
  stale.target.step.maps[ghost].value={op:'if',c:same(next,n(0)),then:get(ghost,r.point),else:next}
  assert(!checkGhostWrite(machine,law,stale),'stale removal contribution accepted')
  const projection=structuredClone(certificate)
  projection.projection.omitMap=r.group
  assert(!checkGhostWrite(machine,law,projection),'projection omitted original field')
  const dropped=structuredClone(certificate)
  delete dropped.target.maps[r.group]
  assert(!checkGhostWrite(machine,law,dropped),'target omitted original field')
  assert(ghostWriteTheory(machine,law,certificate))
}
writeFileSync(`${process.env.SUPERCOMPUTER_OUTPUT_DIR}/certificate.json`,JSON.stringify(p))
console.log(JSON.stringify({item,id,node:process.version,ms,kind:certificate.kind,kindConjuncts:kinds?.laws.length??0,proven:result.proven,checked:result.checked}))
writeFileSync(file,toLean([{id:'Replay',aggregate:{source:machine,law,certificate,kinds}}],{native:false}))
