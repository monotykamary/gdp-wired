import {expect,test} from 'bun:test'
import {auditCostWins} from './cost-wins-audit.ts'
const manifest={baselineCommit:'50109a36',kernelEqual:true,harnessEqual:true}
const fixture=()=>['A1','B1','A2','B2','A3','B3'].map((id,i)=>({id,side:id[0]!,repeat:Number(id[1]),exitCode:0,total:{wallMs:50},laws:['one primary','Inv3915','Inv1758','Inv2973','Inv*'].map((law,j)=>({law,proven:j<3,checked:j<3,wallMs:10+i,countedMs:100,cache:id[0]==='B'?{retargetChecks:2,retargetHits:1,independentChecks:2,independentHits:1}:null}))}))
test('audits all thirty verdicts and median/max of three',()=>{const x=auditCostWins(fixture(),manifest);expect(x.lawResults).toBe(30);expect(x.laws[0]!.A.wallMedianMs).toBe(12);expect(x.laws[0]!.B.wallMaxMs).toBe(15)})
test('does not accept changed verdicts',()=>{const r=fixture();r[3]!.laws[4]!.proven=true;expect(()=>auditCostWins(r,manifest)).toThrow()})
test('does not accept missing repeats or duplicate laws',()=>{expect(()=>auditCostWins(fixture().slice(1),manifest)).toThrow();const r=fixture();r[0]!.laws[1]!.law='one primary';expect(()=>auditCostWins(r,manifest)).toThrow()})
test('does not accept absent or impossible cache counters',()=>{const r=fixture();r[1]!.laws[0]!.cache!.retargetHits=3;expect(()=>auditCostWins(r,manifest)).toThrow();r[1]!.laws[0]!.cache=null;expect(()=>auditCostWins(r,manifest)).toThrow()})
test('does not accept changed kernel or harness',()=>{expect(()=>auditCostWins(fixture(),{...manifest,kernelEqual:false})).toThrow();expect(()=>auditCostWins(fixture(),{...manifest,harnessEqual:false})).toThrow()})
