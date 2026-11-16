import {expect,test} from 'bun:test'
import {nat,rule} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'
import {rel} from '../protocols/ic3syn/common.ts'
import {restateSeeds} from './candidate-seed-restatement.ts'

test('regenerates a packed kind law from the target native kind instead of dropping it',()=>{
 const r=rule('native kinds').params({size:nat}).maps({Edges:rel})
 const source:Law={name:'every OldEdges cell is a value of its kind',forall:'oldKey',holds:{op:'<=',a:{op:'get',map:'OldEdges',key:{op:'var',name:'oldKey'}},b:{op:'const',value:1}}}
 const binding={maps:{OldEdges:{target:'Edges',sorts:['Node','Node'],radix:64}},domains:{Node:'size'}}
 const expanded=restateSeeds([source],r.machine,binding)[0]
 expect(expanded?.status).toBe('candidate')
 expect(expanded?.status==='candidate'&&expanded.expandedKind).toBe('Edges')
 const native=r.kindLaws(), [a]=restateSeeds([source],r.machine,binding,{kindLaws:native})
 expect(a?.status).toBe('candidate')
 if(a?.status!=='candidate')throw Error('native kind was not proposed')
 expect(a.regeneratedKind).toBe('Edges')
 expect(a.law.holds).toEqual(native.find(l=>l.name==='every Edges cell is a value of its kind')!.holds)
 expect(a.law.name).toBe('retained:0:every OldEdges cell is a value of its kind')
 expect(restateSeeds([source],{...r.machine,maps:{}},binding,{kindLaws:native})[0]?.status).toBe('dropped')
})
