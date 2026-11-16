import {expect,test} from 'bun:test'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {dataText,readLiftSource,assertSourceMatches,sourceStructure,sourceLeanId,type GenericLiftSource} from './source.ts'
import {selectGenericLiftRoute,assertGenericBridgeShape} from './shape.ts'
import {projectionOf,type ProvenanceBundle,type FamilyBundle} from './proof-capture.ts'

const machine={name:'source',params:[],inputs:[],state:{},step:{}}
const law={name:'true',holds:{op:'<=' as const,a:{op:'const' as const,value:0},b:{op:'const' as const,value:0}}}
function plain():ProvenanceBundle {
  const b:ProvenanceBundle={schema:'bapa-proof/v1',route:'plain',identity:{protocol:'any'} as ProvenanceBundle['identity'],original:{machine:structuredClone(machine),laws:[structuredClone(law)]},terms:{terms:[],identities:[]},verdict:{proven:true,checked:true},projection:{kind:'same-machine',publicLawIndices:[0]},proof:{kind:'usual',machine:structuredClone(machine),laws:[structuredClone(law)],proof:{instances:{},trees:{}}}}
  b.projection=projectionOf(b);return b
}
const source=(b=plain()):GenericLiftSource=>({schema:'gdp-lift-source/v1',id:'unrelated_output_label',...structuredClone(b.original)})
test('portable data bytes preserve exact UTF-8 decoding and BOM rejection',()=>{
  for(const bytes of [Uint8Array.of(0xef,0xbb,0xbf,0x7b,0x7d),Uint8Array.of(0xe2,0x82,0xac),Uint8Array.of(0xff,0x61)]){
    expect(dataText(bytes)).toBe(Buffer.from(bytes).toString('utf8'))
  }
  expect(()=>JSON.parse(dataText(Uint8Array.of(0xef,0xbb,0xbf,0x7b,0x7d)))).toThrow()
})
test('shape dispatch and output naming are independent of protocol and source ids',()=>{
  for(const id of ['toy_consensus_forall','client_server_db_ae','simple_decentralized_lock','unknown']){
    const b=plain();b.identity={...b.identity,protocol:id}
    expect(selectGenericLiftRoute(b)).toBe('alpha')
    const s={...source(b),id};assertSourceMatches(s,b)
    expect(sourceLeanId(id)).toBe('bapa_'+id)
  }
  expect(()=>sourceLeanId('a/b')).toThrow('unsafe');expect(()=>sourceLeanId('λ/../../')).toThrow('unsafe')
})
test('counted augmentation and witness provenance choose semantic routes',()=>{
  const p=plain(),producer={...machine,counts:{n:{j:'j',key:'k',below:{op:'const' as const,value:0},body:{op:'const' as const,value:0}}}}
  const b:FamilyBundle={schema:'bapa-family/v1',route:'counted-family',original:p.original,identity:p.identity,verdict:p.verdict,terms:p.terms,projection:{kind:'unqualified',reason:'augmented'},publicLawIndices:[0],final:{phase:'closed-family',checked:true,machine:producer,laws:p.original.laws,proof:{instances:{},certs:{}}}}
  expect(selectGenericLiftRoute(b)).toBe('counted');assertGenericBridgeShape(b,'counted')
  const w=plain();w.route='witness';w.original.laws[0]={...law,some:['w']};w.proof={kind:'derived',parents:[w.proof],context:{kind:'skolem'} as never}
  expect(selectGenericLiftRoute(w)).toBe('witness')
})
test('exact original AST and metadata are bound, not just law names',()=>{
  const b=plain();assertSourceMatches(source(b),b)
  for(const mutate of [
    (s:GenericLiftSource)=>{s.machine.name='renamed'},
    (s:GenericLiftSource)=>{s.machine.assume=law.holds},
    (s:GenericLiftSource)=>{s.laws[0]!.holds={op:'=' as const,a:{op:'const',value:0},b:{op:'const',value:1}}},
    (s:GenericLiftSource)=>{s.laws[0]!.keys=['other']},
    (s:GenericLiftSource)=>{s.laws[0]!.some=['w']},
  ]){const s=source(b);mutate(s);expect(()=>assertSourceMatches(s,b)).toThrow('differs')}
})
test('undefined optional properties are normalized, all other metadata retained',()=>{
  expect(sourceStructure({a:1,b:undefined})).toBe(sourceStructure({a:1}))
  expect(sourceStructure({a:1,b:{}})).not.toBe(sourceStructure({a:1}))
  for(const x of [()=>1,{f:()=>1},[undefined],NaN,-0,2n,new Map()])expect(()=>sourceStructure(x)).toThrow()
  let invoked=false;const accessor=Object.defineProperty({},'a',{enumerable:true,get(){invoked=true;return 1}})
  expect(()=>sourceStructure(accessor)).toThrow('accessors');expect(invoked).toBe(false)
})
test('unsupported special semantics refuse by shape, with no registry fallback',()=>{
  for(const change of ['functions','history','sums','finite','some','mixed']){
    const b=plain()
    if(change==='functions')b.original.machine.fns={f:{js:'() => 0'}}
    if(change==='history')b.original.machine.history={} as never
    if(change==='sums')b.original.machine.sums={s:{} as never}
    if(change==='finite')b.original.laws[0]!.finite='n'
    if(change==='some')b.original.laws[0]!.some=['w']
    if(change==='mixed')b.proof={kind:'derived',context:{kind:'projection'},parents:[b.proof,{...b.proof}]}
    expect(()=>selectGenericLiftRoute(b)).toThrow('unsupported')
  }
  const b=plain();if(b.proof.kind!=='usual')throw Error('fixture');b.proof.machine.state={s:{op:'const',value:0}}
  expect(()=>assertGenericBridgeShape(b,'alpha')).toThrow('unsupported source-to-family')
})
test('JSON ABI rejects code envelopes, empty laws and functions without executing code',()=>{
  const root=mkdtempSync(join(tmpdir(),'lift-source-')),file=join(root,'source.json')
  try {
    writeFileSync(file,JSON.stringify(source()));expect(readLiftSource(file).source.schema).toBe('gdp-lift-source/v1')
    for(const x of [{...source(),schema:'js'}, {...source(),laws:[]}, {...source(),code:'throw Error()'}, {...source(),machine:{...machine,fns:{f:{js:'() => 0'}}}}]){
      writeFileSync(file,JSON.stringify(x));expect(()=>readLiftSource(file)).toThrow()
    }
    writeFileSync(file,'export default 1');expect(()=>readLiftSource(file)).toThrow()
    writeFileSync(file,JSON.stringify(source()));expect(()=>readLiftSource(file,1)).toThrow('oversized')
  } finally {rmSync(root,{recursive:true,force:true})}
})
