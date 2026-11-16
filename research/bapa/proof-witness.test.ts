import {describe,expect,it} from 'bun:test'
import {ghostedMachine,obligations,leafConstraints} from '../../kernel/kernel.ts'
import type {ProvenanceBundle} from './proof-capture.ts'
import {syntheticPlain} from './proof-synthetic.ts'
import {exportWitnessSource} from './proof-witness.ts'
import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {leanProject} from '../../lean-kernel/emit.ts'

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
function boundFixture():ProvenanceBundle {
  const b=fixture()
  // The only valid chosen witness is 0: changing one branch to 1 must fail.
  b.original.laws[0]!.holds={op:'<=',a:{op:'var',name:'w'},b:{op:'const',value:0}}
  return b
}
function branches():ProvenanceBundle {
  const a=boundFixture(), b=boundFixture()
  return {...a,proof:{kind:'derived',context:{kind:'projection'},parents:[a.proof,b.proof]}}
}
describe('complete witness parent coverage',()=>{
  it('checks and conjoins both source and whole-family theorems',()=>{
    const out=exportWitnessSource(branches(),'multi_control')
    expect(out.parentPaths).toHaveLength(2)
    expect(out.publicBridge).toContain('And.intro (@multi_control_path0_ex0) ((@multi_control_path1_ex0))')
    expect(out.publicBridge).toContain('And.intro (@multi_control_path0_laws) ((@multi_control_path1_laws))')
    expect(out.sourceTheorems[0]?.name).toBe('multi_control_ex0')
    const directory=process.env.BAPA_MULTIPARENT_CONTROL
    if(directory){
      mkdirSync(directory,{recursive:true})
      const body='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\n'+out.body+'\n'+out.publicBridge+'\n#print axioms multi_control_ex0\n#print axioms multi_control_laws\n'
      for(const [name,text]of Object.entries(leanProject(body,{name:'BapaProof'})))writeFileSync(join(directory,name),text)
      const bad=body.split('\n').map(line=>line.startsWith('  forall_some_of_ghostsubst_bound multi_control_path1_gm ')
        ? line.replace(/\[\((\d+), \.const 0\)\]/,'[($1, .const 1)]') : line).join('\n')
      expect(bad).not.toBe(body)
      mkdirSync(directory+'-bad-second',{recursive:true})
      for(const [name,text]of Object.entries(leanProject(bad,{name:'BapaProof'})))writeFileSync(join(directory+'-bad-second',name),text)
    }
  })
  it('refuses a witness wrong only on the second parent',()=>{
    const b=branches()
    if(b.proof.kind!=='derived'||b.proof.parents[1]?.kind!=='derived')throw Error('fixture')
    const c=b.proof.parents[1].context as {plains:Record<string,{sub:Record<string,unknown>}>}
    Object.values(c.plains)[0]!.sub.w={op:'const',value:1}
    expect(()=>exportWitnessSource(b,'bad_witness')).toThrow('invalid captured skolem plain')
  })
  it('refuses a broken proof only on the second parent',()=>{
    const b=branches()
    if(b.proof.kind!=='derived'||b.proof.parents[1]?.kind!=='derived'||b.proof.parents[1].parents[0]?.kind!=='usual')throw Error('fixture')
    b.proof.parents[1].parents[0].proof.trees={}
    expect(()=>exportWitnessSource(b,'bad_proof')).toThrow('does not check')
  })
  it('checks an inferred parent using the unique retained sibling context',()=>{
    const b=boundFixture()
    if(b.proof.kind!=='derived'||b.proof.parents[0]?.kind!=='usual')throw Error('fixture')
    const leaf=b.proof.parents[0]
    const inf={kind:'derived' as const,context:{kind:'inference',original:leaf.machine,laws:leaf.laws},parents:[leaf]}
    b.proof={kind:'derived',context:{kind:'projection'},parents:[inf,b.proof]}
    expect(exportWitnessSource(b,'inferred_control').parentPaths).toHaveLength(2)
    inf.context.original={...inf.context.original,name:'changed'}
    expect(()=>exportWitnessSource(b,'bad_inference')).toThrow('inference parent differs')
  })
  it('refuses cyclic, missing or duplicate parents instead of ignoring them',()=>{
    const b=branches()
    if(b.proof.kind!=='derived')throw Error('fixture')
    b.proof.parents[1]=b.proof
    expect(()=>exportWitnessSource(b,'cycle')).toThrow('cyclic')
    b.proof.parents[1]=undefined
    expect(()=>exportWitnessSource(b,'missing')).toThrow('missing')
    b.proof.parents[1]=b.proof.parents[0]
    expect(()=>exportWitnessSource(b,'duplicate')).toThrow('duplicate')
  })
})

function constantProof(leaf:Extract<ProvenanceBundle['proof'],{kind:'usual'}>):void {
  // Synthetic constant contradictions only: no prover/search call.
  leaf.proof={instances:{},trees:Object.fromEntries(obligations(leaf.machine,leaf.laws).map(g=>{
    const index=leafConstraints(g,new Map()).findIndex(r=>Object.keys(r.lin).every(k=>k==='1')&&(r.lin['1']??0)>0)
    if(index<0)throw Error('fixture contradiction absent')
    return [g.name,{leaf:[{kind:'input' as const,index}]}]
  }))}
}
function sourceInferenceFixture():ProvenanceBundle {
  const b=boundFixture()
  if(b.proof.kind!=='derived'||b.proof.parents[0]?.kind!=='usual')throw Error('fixture')
  const leaf=b.proof.parents[0], seed={...leaf.laws[0]!,name:'retained seed'}
  leaf.laws.push(seed)
  constantProof(leaf)
  b.proof={kind:'derived',parents:[b.proof],context:{kind:'inference',original:b.original.machine,laws:[...b.original.laws,seed]}}
  return b
}
function alphaSourceFixture():ProvenanceBundle {
  const b=sourceInferenceFixture()
  if(b.proof.kind!=='derived'||b.proof.parents[0]?.kind!=='derived'||b.proof.parents[0].parents[0]?.kind!=='usual')throw Error('fixture')
  const witness=b.proof.parents[0],leaf=witness.parents[0]!
  if(leaf.kind!=='usual')throw Error('fixture')
  const variant=(q:string,r:string):ProvenanceBundle['original']['machine']=>({...b.original.machine,maps:{R:0},step:{...b.original.machine.step,
    flags:{q:{op:'all',key:q,c:{op:'<=',a:{op:'const',value:0},b:{op:'var',name:q}}}},
    maps:{R:{each:r,value:{op:'get',map:'R',key:{op:'var',name:r}}}}}})
  const producer=variant('producerQ','producerRow'),source=variant('sourceQ','sourceRow')
  const c=witness.context as {original:typeof producer,G:{orig:typeof producer,vars:{},maps:{}}}
  c.original=producer;c.G.orig=producer;leaf.machine=ghostedMachine(c.G);constantProof(leaf)
  ;(b.proof.context as {original:typeof producer}).original=producer
  b.original={...b.original,machine:source}
  return b
}
describe('checked witness source alpha transport',()=>{
  it('records QAlpha and RowAlpha proposals and transports the original existential',()=>{
    const out=exportWitnessSource(alphaSourceFixture(),'alpha_control')
    expect(out.status).toBe('EMITTED_NOT_CHECKED')
    expect(out.alphaTransports?.[0]?.renames).toEqual([{flag:'q',old:'sourceQ',fresh:'producerQ'}])
    expect(out.alphaTransports?.[0]?.rows).toEqual([{map:'R',old:'sourceRow',fresh:'producerRow'}])
    expect(out.sourceTheorems[0]?.name).toBe('alpha_control_ex0')
    expect(out.body).toContain('SReach alpha_control_source')
    expect(out.body).toContain('Kern.QAlpha.renameAll_equiv')
    expect(out.body).toContain('Kern.RowAlpha.renameAll_equiv')
    const directory=process.env.BAPA_SOURCE_ALPHA_CONTROL
    if(directory){
      const names=['alpha_control_ex0','alpha_control_laws',...out.alphaTransports!.flatMap(a=>a.theorems)]
      const body='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\n'+out.body+'\n'+out.publicBridge+'\n'+names.map(n=>'#print axioms '+n).join('\n')+'\n'
      for(const [suffix,text]of [['',body],['-bad-renaming',body.replace(/^(def alpha_control_source_renames .* := )\[.*\]$/m,'$1[]')]]){
        if(suffix)expect(text).not.toBe(body)
        mkdirSync(directory+suffix,{recursive:true})
        for(const [name,content]of Object.entries(leanProject(text!,{name:'BapaProof'})))writeFileSync(join(directory+suffix!,name),content)
      }
    }
  })
  it('rejects a non-alpha transition difference even alongside valid binder renames',()=>{
    const b=alphaSourceFixture()
    b.original.machine={...b.original.machine,step:{...b.original.machine.step,state:{s:{op:'const',value:1}}}}
    expect(()=>exportWitnessSource(b,'bad_nonalpha')).toThrow('source inference original differs')
  })
})

describe('source inference witness wrappers',()=>{
  it('checks source custody and proves retained seeds rather than assuming them',()=>{
    const out=exportWitnessSource(sourceInferenceFixture(),'source_inference_control')
    expect(out.status).toBe('EMITTED_NOT_CHECKED')
    expect(out.body).toContain('source_inference_control_e1')
    expect(out.sourceTheorems[0]?.type).toBe('exists')
    const directory=process.env.BAPA_SOURCE_INFERENCE_CONTROL
    if(directory){
      mkdirSync(directory,{recursive:true})
      const body='import QAlpha\nimport Ghost\nimport GhostMap\nopen Kern Cert\n'+out.body+'\n'+out.publicBridge+'\n#print axioms source_inference_control_ex0\n#print axioms source_inference_control_laws\n'
      for(const [name,text]of Object.entries(leanProject(body,{name:'BapaProof'})))writeFileSync(join(directory,name),text)
    }
  })
  it('refuses a wrapper whose original source transition differs',()=>{
    const b=sourceInferenceFixture()
    if(b.proof.kind!=='derived')throw Error('fixture')
    const c=b.proof.context as {original:ProvenanceBundle['original']['machine']}
    c.original={...c.original,step:{...c.original.step,state:{s:{op:'const',value:1}}}}
    expect(()=>exportWitnessSource(b,'bad_source')).toThrow('source inference original differs')
  })
  it('refuses missing, changed or duplicated public source laws',()=>{
    for(const variant of ['missing','changed','duplicate']){
      const b=sourceInferenceFixture()
      if(b.proof.kind!=='derived')throw Error('fixture')
      const c=b.proof.context as {laws:ProvenanceBundle['original']['laws']}
      if(variant==='missing')c.laws=c.laws.slice(1)
      else if(variant==='changed')c.laws=[{...c.laws[0]!,holds:{op:'and',xs:[]}},...c.laws.slice(1)]
      else c.laws.push(c.laws[0]!)
      expect(()=>exportWitnessSource(b,'bad_public')).toThrow('source inference public laws')
    }
  })
  it('refuses an extra claim not proved in the complete family',()=>{
    const b=sourceInferenceFixture()
    if(b.proof.kind!=='derived')throw Error('fixture')
    ;(b.proof.context as {laws:ProvenanceBundle['original']['laws']}).laws.push({name:'unproved extra',holds:{op:'and',xs:[]}})
    expect(()=>exportWitnessSource(b,'bad_extra')).toThrow('extra law absent')
  })
  it('refuses a retained seed whose certificate was removed',()=>{
    const b=sourceInferenceFixture()
    if(b.proof.kind!=='derived'||b.proof.parents[0]?.kind!=='derived'||b.proof.parents[0].parents[0]?.kind!=='usual')throw Error('fixture')
    delete b.proof.parents[0].parents[0].proof.trees['retained seed @step']
    expect(()=>exportWitnessSource(b,'bad_seed')).toThrow('does not check')
  })
})

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
