import {describe,expect,it} from 'bun:test'
import {ghostedMachine} from '../../kernel/kernel.ts'
import type {ProvenanceBundle} from './proof-capture.ts'
import {syntheticPlain} from './proof-synthetic.ts'
import {exportWitnessSource} from './proof-witness.ts'

function fixture():ProvenanceBundle {
  const p = syntheticPlain(), G = {orig:p.machine,vars:{},maps:{}}
  const law = {...p.laws[0]!,some:['w']}, plain = p.laws[0]!
  const leaf = {kind:'usual' as const,machine:ghostedMachine(G),laws:[plain],proof:p.proof}
  return {schema:'bapa-proof/v1',route:'witness',identity:{} as ProvenanceBundle['identity'],
    original:{machine:p.machine,laws:[law]},verdict:{proven:true,checked:true},terms:{terms:[],identities:[]},
    projection:{kind:'unqualified',reason:'control'},proof:{kind:'derived',parents:[leaf],context:
      {kind:'skolem',original:p.machine,laws:[law],G,plains:{[law.name]:{plain,sub:{w:{op:'const',value:0}}}},family:[plain]}}}
}
function legacyWitness():ProvenanceBundle {
  const b=fixture()
  if(b.proof.kind!=='derived' || b.proof.parents[0]?.kind!=='usual') throw Error('fixture')
  const leaf=b.proof.parents[0], source=b.original.laws[0]!
  const plain={...leaf.laws[0]!,ex:{vars:source.some!,body:source.holds,sub:{w:{op:'const' as const,value:0}}}}
  leaf.laws=[plain]
  b.proof.context={kind:'witness',original:b.original.machine,laws:[{...source,witness:{}}],
    machine:leaf.machine,plain:leaf.laws,ghosts:[]}
  return b
}
describe('witness source custody',()=>{
  it('uses the original public law while ignoring only retained witness advice',()=>{
    const b=legacyWitness(), r=exportWitnessSource(b,'legacy_control')
    expect(r.sourceTheorems[0]?.type).toBe('exists')
    expect(r.body).toContain('forall_some_of_ghostsubst_bound')
    if(b.proof.kind!=='derived') throw Error('fixture')
    const c=b.proof.context as {laws:typeof b.original.laws}
    c.laws[0]={...c.laws[0]!,holds:{op:'and',xs:[]}}
    expect(()=>exportWitnessSource(b,'legacy_control')).toThrow('differs')
  })
  it('does not ignore a missing original member of the witness context',()=>{
    const b=legacyWitness()
    if(b.proof.kind!=='derived') throw Error('fixture')
    ;(b.proof.context as {laws:unknown[]}).laws=[]
    expect(()=>exportWitnessSource(b,'legacy_control')).toThrow()
  })
  it('emits an existential source theorem without claiming Lean checked it',()=>{
    const r=exportWitnessSource(fixture(),'witness_control')
    expect(r.status).toBe('EMITTED_NOT_CHECKED')
    expect(r.sourceTheorems[0]?.name).toBe('witness_control_ex0')
    expect(r.body).toContain('theorem witness_control_ex0')
    expect(r.publicLawIndices).toEqual([0])
  })
  it('rejects changed original and ambiguous custody',()=>{
    const a=fixture(); a.original={...a.original,machine:{...a.original.machine,name:'other'}}
    expect(()=>exportWitnessSource(a,'witness_control')).toThrow()
    const b=fixture(); if(b.proof.kind!=='derived') throw Error('fixture')
    b.proof.parents.push(b.proof.parents[0]); expect(()=>exportWitnessSource(b,'witness_control')).toThrow()
  })
  it('rejects unsupported public law semantics and annotated projections',()=>{
    for(const extra of [{stated:{}},{some:[]},{ex:{}},{finite:'size'},{witness:{}}]){
      const a=fixture(); Object.assign(a.original.laws[0]!,extra)
      expect(()=>exportWitnessSource(a,'witness_control')).toThrow()
    }
    const b=fixture(); b.proof={kind:'derived',parents:[b.proof],context:{kind:'projection',unverified:true}}
    expect(()=>exportWitnessSource(b,'witness_control')).toThrow('unsupported')
  })
  it('rejects a fabricated plain object and invalid tree',()=>{
    const a=fixture(); if(a.proof.kind!=='derived') throw Error('fixture')
    const c=a.proof.context as {plains:Record<string,{plain:object}>}; const q=Object.values(c.plains)[0]!
    q.plain={...q.plain}; expect(()=>exportWitnessSource(a,'witness_control')).toThrow()
    const b=fixture(); if(b.proof.kind!=='derived' || b.proof.parents[0]?.kind!=='usual') throw Error('fixture')
    b.proof.parents[0].proof.trees={}; expect(()=>exportWitnessSource(b,'witness_control')).toThrow()
  })
})
