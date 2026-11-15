import {expect,test} from 'bun:test'
import {proofOutput,retainFamily,retainFrom,publishProof,type PublicProofOutput} from './proof-output.ts'
import type {Machine,Law} from './machine.ts'
const machine={} as Machine,laws=[] as Law[],proof={instances:{},trees:{}}
test('default-off output hooks preserve result identity and add no public keys',()=>{
 proofOutput.on=undefined;const out={proven:true,checked:true},keys=Object.keys(out)
 expect(retainFamily(out,machine,laws,proof)).toBe(out);expect(retainFrom(out,[out])).toBe(out);expect(publishProof(out,machine,laws)).toBe(out);expect(Object.keys(out)).toEqual(keys)
})
test('actual producer links follow returned objects and reset between invocations',()=>{
 let event:PublicProofOutput|undefined
 const listener=(e:PublicProofOutput)=>{event=e}
 proofOutput.on=listener
 try{const first=retainFamily({proven:true,checked:true},machine,laws,proof);const result=retainFrom({...first},[first]);publishProof(result,machine,laws);expect(event!.proof!.kind).toBe('derived')
 proofOutput.on=undefined;proofOutput.on=listener
 const stale=retainFrom({...first},[first]);publishProof(stale,machine,laws);expect((event!.proof as any).parents).toEqual([undefined])
 }finally{proofOutput.on=undefined}
})
test('unproven or unchecked families confer no provenance',()=>{
 let event:PublicProofOutput|undefined;proofOutput.on=e=>{event=e}
 try{for(const out of [{proven:false,checked:true},{proven:true,checked:false}]){retainFamily(out,machine,laws,proof);publishProof(out,machine,laws);expect(event!.proof).toBeUndefined()}}finally{proofOutput.on=undefined}
})
