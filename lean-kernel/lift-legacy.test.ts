import {expect,test} from 'bun:test'
import {validateLegacyEnvelope,validateLegacyManifest} from './lift-legacy.ts'

const h='1'.repeat(64),revision='2'.repeat(40)
const identity={protocol:'test',invocation:'test/1',sourceCommit:revision,sourceTree:revision,driverSha256:h,inputSha256:h,runtimeSha256:h,profileSha256:h,workNumerator:'0',workDenominator:'1',flags:{GDP_TEST:'1'}}
const machine={name:'test',params:[],inputs:[],state:{},step:{state:{}}}
const law={name:'holds',holds:{op:'and',xs:[]}}
function fixture(){
  const manifest=validateLegacyManifest({schema:'final29-native-certificate/v1',complete:true,route:'counted-family',identity,graphManifestSha256:h,terms:0,familyLaws:1,certificateKeys:['holds @start','holds @step'],publicLawIndices:[0]})
  const data={schema:'final29-family/v1',route:'counted-family',identity,original:{machine,laws:[law]},verdict:{proven:true,checked:true},terms:{terms:[],identities:[]},publicLawIndices:[0],final:{phase:'closed-family',checked:true,machine,laws:[law],proof:{certs:{'holds @start':{},'holds @step':{}},instances:{'holds @start':{},'holds @step':{}}}}}
  return {manifest,data}
}
test('historical import preserves schema, identity and object references',()=>{
  const {manifest,data}=fixture(),bundle=validateLegacyEnvelope(manifest,data)
  expect(Object.is(bundle,data)).toBe(true)
  expect(bundle.schema).toBe('final29-family/v1')
  expect(bundle.identity).toBe(identity)
  expect('workBudget'in bundle.identity).toBe(false)
})
test('historical manifest rejects incomplete input and invented work budgets',()=>{
  const {manifest}=fixture()
  for(const patch of [{complete:false},{schema:'bapa-native-certificate/v1'},{route:'other'},{terms:-1},{graphManifestSha256:'x'},{identity:{...identity,workDenominator:'0'}},{identity:{...identity,workNumerator:undefined,workBudget:'1'}}])expect(()=>validateLegacyManifest({...manifest,...patch})).toThrow()
})
test('historical import refuses envelope, term and family mismatches',()=>{
  const {manifest,data}=fixture()
  for(const patch of [{route:'inferred'},{schema:'bapa-family/v1'},{verdict:{proven:true,checked:false}},{identity:{...identity,invocation:'other'}},{terms:{terms:[{}],identities:[]}},{publicLawIndices:null},{final:{...data.final,checked:false}},{final:{...data.final,phase:'partial'}},{final:{...data.final,proof:{...data.final.proof,certs:{'holds @start':{}}}}},{final:{...data.final,proof:{...data.final.proof,instances:null}}}])expect(()=>validateLegacyEnvelope(manifest,{...data,...patch})).toThrow()
})
test('historical import refuses public coverage and duplicate family names',()=>{
  const {manifest,data}=fixture()
  expect(()=>validateLegacyEnvelope({...manifest,publicLawIndices:[]},{...data,publicLawIndices:[]})).toThrow('coverage')
  expect(()=>validateLegacyEnvelope({...manifest,familyLaws:2},{...data,final:{...data.final,laws:[law,law]}})).toThrow('ambiguous')
})
test('historical provenance route must be derived from the actual proof graph',()=>{
  const {manifest}=fixture()
  const outer=validateLegacyManifest({...manifest,route:'inferred'})
  const value={schema:'final29-proof/v1',route:'inferred',identity,original:{machine,laws:[law]},verdict:{proven:true,checked:true},terms:{terms:[],identities:[]},proof:{kind:'usual',machine,laws:[law],proof:{instances:{},trees:{}}}}
  expect(()=>validateLegacyEnvelope(outer,value)).toThrow('provenance route')
  const plain=validateLegacyManifest({...outer,route:'plain'})
  const body={...value,route:'plain'}
  expect(Object.is(validateLegacyEnvelope(plain,body),body)).toBe(true)
})
