import {test,expect} from 'bun:test'
import {gzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {auditPreflight} from './audit-preflight.ts'
import {meterKeys} from './contract.ts'
const zero=()=>Object.fromEntries(meterKeys.map(k=>[k,0]))
const fixture=()=>{
 const weights=Object.fromEntries(meterKeys.slice(12).map(k=>[k,1])),raw={...zero(),evals:15000001}
 const small={id:2,parentId:1,name:'small',depth:1,completed:false,raw,exclusiveRaw:raw,units:15000001,exclusiveUnits:15000001,wallMs:1,exclusiveWallMs:1,unitModel:'explicit-complete',weights}
 const root={...small,id:1,parentId:null,name:'original-protocol',depth:0,completed:true,exclusiveRaw:zero(),exclusiveUnits:0,wallMs:2}
 return{source:'cd00524f01093838e9584edc4a20f71e2be10e2a',id:'consensus_epr',variant:'original',repetition:1,work:15000000,weights,raw,result:{verdict:'unknown'},budgetExhausted:true,events:[small,root]}
}
const seal=(data:any)=>{const bytes=Buffer.from(JSON.stringify(data));return{...data,phaseEvents:data.events,sha256:createHash('sha256').update(bytes).digest('hex'),receiptGzipBase64:gzipSync(bytes).toString('base64')}}
test('complete phase receipt verifies and attributes units',()=>{const d=fixture();expect(auditPreflight(seal(d),d).diagnosticUnits).toBe(15000001)})
test('wrong receipt hash is rejected',()=>{const d=fixture(),r=seal(d);r.sha256='bad';expect(()=>auditPreflight(r,d)).toThrow()})
test('mismatched preserved raw is rejected',()=>{const d=fixture();expect(()=>auditPreflight(seal(d),{...d,raw:zero()})).toThrow()})
test('price changes cannot masquerade as original diagnostic weights',()=>{const d=fixture();d.weights.evals=2;expect(()=>auditPreflight(seal(d),d)).toThrow()})
test('false event units are rejected independently',()=>{const d=fixture();d.events[0]!.units=0;expect(()=>auditPreflight(seal(d),d)).toThrow()})
test('completed small phase cannot stand in for exhaustion',()=>{const d=fixture();d.events[0]!.completed=true;expect(()=>auditPreflight(seal(d),d)).toThrow()})
