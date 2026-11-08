import {test,expect} from 'bun:test'
import {auditSection10Gate} from './section10-gate-audit.ts'
const manifest={kernelEqual:true,harnessEqual:true,baselineCommit:'50109a36'}
const records=()=>['A1','B1','A2','B2','A3','B3'].map(id=>({id,side:id[0],repeat:Number(id[1]),exitCode:0,total:{wallMs:50000+Number(id[1])},laws:Array.from({length:5},(_,i)=>({law:'law'+i,proven:i<3,checked:i<3,wallMs:1000*Number(id[1]),countedMs:100+i}))}))
test('the audit computes median/max and preserves every count',()=>{const r=auditSection10Gate(records(),manifest);expect(r.laws[0]!.B.wallMedianMs).toBe(2000);expect(r.laws[0]!.B.wallMaxMs).toBe(3000);expect(r.laws[0]!.B.countedUnits).toEqual([100,100,100]);expect(r.noRegression).toBe(true);expect(r.gate1ReplayPass).toBe(false)})
test('a missing repeat cannot yield a median-of-three table',()=>expect(()=>auditSection10Gate(records().slice(1),manifest)).toThrow())
test('nonfinite counted work is rejected',()=>{const rs=records();rs[1]!.laws[0]!.countedMs=NaN;expect(()=>auditSection10Gate(rs,manifest)).toThrow()})
test('any checked-law loss is a regression',()=>{const rs=records();rs[3]!.laws[1]!.checked=false;expect(auditSection10Gate(rs,manifest).noRegression).toBe(false)})
test('a checked family beyond sixty seconds does not pass',()=>{const rs=records();for(const r of rs)for(const l of r.laws)l.proven=l.checked=true;rs[5]!.total.wallMs=60001;expect(auditSection10Gate(rs,manifest).gate1ReplayPass).toBe(false)})
test('a new baseline must be explicitly named, never silently accepted',()=>{
 const changed={...manifest,baselineCommit:'192ebbe2'}
 expect(()=>auditSection10Gate(records(),changed)).toThrow()
 expect(auditSection10Gate(records(),changed,'192ebbe2').baseline).toBe('192ebbe2')
})

test('kernel drift cannot pass an evidence audit',()=>expect(()=>auditSection10Gate(records(),{...manifest,kernelEqual:false})).toThrow())
