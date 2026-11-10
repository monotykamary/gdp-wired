import {expect,test} from 'bun:test'
import {n,x} from '../../core/machine.ts'
import {type CountCert} from '../../kernel/kernel.ts'
import {compensatedTransportIndices,shadowedTransportIndices} from './prefer-compensated.ts'
function packet():Pick<CountCert,'reads'|'insts'>{
 const below=x('size'),q=(terms:CountCert['insts'][number]['terms'])=>({wit:'w',below,terms,unit:0})
 return {reads:[['post','A#',x('row')],['old','A',x('row')],['request','R',n(0)]],insts:[q([[1,'post'],[-1,'request']]),q([[1,'post'],[-1,'old']]),q([[1,'post'],[-1,'old'],[-1,'request']])]}
}
test('compensation shadows only the unqualified request transport proposal',()=>{
 const p=packet(),snapshot=JSON.stringify(p)
 expect([...shadowedTransportIndices(p)]).toEqual([0])
 expect([...compensatedTransportIndices(p)]).toEqual([2])
 expect(JSON.stringify(p)).toBe(snapshot)
 expect([...shadowedTransportIndices({...p,insts:p.insts.slice(0,2)})]).toEqual([])
})
test('preference is independent of names and term order',()=>{
 const p=packet(),names=new Map([['post','z'],['old','x'],['request','y']])
 p.reads=p.reads.map(([id,map,key])=>[names.get(id)!,map.replace('A','Renamed'),key])
 p.insts=p.insts.map(q=>({...q,terms:q.terms.map(([z,id])=>[z,names.get(id)!] as [number,string]).reverse()}))
 expect([...shadowedTransportIndices(p)]).toEqual([0])
})
test('different row or universe does not shadow a proposal',()=>{
 const p=packet();p.reads[1]![2]=x('otherRow')
 expect([...shadowedTransportIndices(p)]).toEqual([])
 const q=packet();q.insts[2]!.below=x('otherSize')
 expect([...shadowedTransportIndices(q)]).toEqual([])
})
test('matching source indices are structural and require known pre-state input reads',()=>{
 const p=packet()
 p.insts.push({...p.insts[2]!,terms:[...p.insts[2]!.terms].reverse()})
 expect([...compensatedTransportIndices(p)]).toEqual([2,3])
 p.reads=p.reads.filter(r=>r[0]!=='request')
 expect([...compensatedTransportIndices(p)]).toEqual([])
})
test('unknown or post-state compensation inputs never receive priority',()=>{
 const p=packet();p.reads[2]![1]='R#'
 expect([...compensatedTransportIndices(p)]).toEqual([])
 const q=packet();q.insts[2]!.unit=1
 expect([...compensatedTransportIndices(q)]).toEqual([])
})
test('nonzero units and non-unit compensation coefficients are not matched',()=>{
 const p=packet();p.insts[2]!.unit=1
 expect([...shadowedTransportIndices(p)]).toEqual([])
 const q=packet();q.insts[2]!.terms[1]![0]=-2
 expect([...shadowedTransportIndices(q)]).toEqual([])
})
