import {expect,test} from 'bun:test'
import {n,x} from './machine.ts'
import {appendCountCert} from './count-cert-grow.ts'
import {type CountCert} from '../kernel/kernel.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
test('growing a certificate preserves every old proof identity and remaps new terms',()=>{
 const old:Proposal={reads:[['r0','A',x('a')]],insts:[{wit:'w0',below:n(4),unit:0,terms:[[1,'r0']]}]}
 const next:Proposal={reads:[['r0','B',x('b')],['r1','A',x('a')]],insts:[{wit:'w0',below:n(4),unit:0,terms:[[1,'r1']]},{wit:'w1',below:n(4),unit:0,terms:[[1,'r0'],[-1,'r1']]}]}
 expect(appendCountCert(old,next,x('countRead$0'))).toBe(true)
 expect(old.reads[0]).toEqual(['r0','A',x('a')])
 expect(old.insts[0]).toEqual({wit:'w0',below:n(4),unit:0,terms:[[1,'r0']]})
 expect(old.reads).toHaveLength(2);expect(old.insts).toHaveLength(2)
 const added=old.reads[1]![0]
 expect(added).not.toBe('r0');expect(added).not.toBe('countRead$0')
 expect(old.insts[1]!.terms).toEqual([[1,added],[-1,'r0']])
 expect(old.insts[1]!.wit).not.toBe('w0')
 expect(appendCountCert(old,next,{})).toBe(false)
 expect(next.reads[0]![0]).toBe('r0')
})
