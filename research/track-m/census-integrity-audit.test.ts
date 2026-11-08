import {describe,test,expect} from 'bun:test'
import {auditIntegrity,type IntegrityRun} from './census-integrity-audit.ts'
const source={productionDifferences:[],installedProductionDifferences:[]}
const first:IntegrityRun={id:'a1',variant:'census-profile',exitCode:0,laws:['one','two','three'].map((law,i)=>({law,proven:true,checked:true,wallMs:100,kernelMs:50,countedUnits:i+1,sites:{'kernel/kernel.ts:checkMC':{calls:3}}}))}
const pair=()=>[structuredClone(first),{...structuredClone(first),id:'b1',variant:'tf1-profile'}]
describe('measurement integrity',()=>{
 test('timing may vary without changing work',()=>{const rows=pair();rows[1]!.laws[0]!.kernelMs=200;expect(auditIntegrity(rows,source)).toHaveLength(6)})
 test('reject changed counted work',()=>{const rows=pair();rows[1]!.laws[0]!.countedUnits++;expect(()=>auditIntegrity(rows,source)).toThrow('different proof work')})
 test('reject changed checker counts',()=>{const rows=pair();rows[1]!.laws[0]!.sites['kernel/kernel.ts:checkMC']!.calls--;expect(()=>auditIntegrity(rows,source)).toThrow('different call counts')})
 test('reject extra instrumented sites',()=>{const rows=pair();rows[1]!.laws[0]!.sites.extra={calls:1};expect(()=>auditIntegrity(rows,source)).toThrow('different call counts')})
 test('reject unchecked results',()=>{const rows=pair();rows[1]!.laws[0]!.checked=false;expect(()=>auditIntegrity(rows,source)).toThrow('unchecked/incomplete')})
 test('reject incomplete runs',()=>{const rows=pair();rows[1]!.laws.pop();expect(()=>auditIntegrity(rows,source)).toThrow('unchecked/incomplete')})
 test('reject changed installed source',()=>expect(()=>auditIntegrity(pair(),{...source,installedProductionDifferences:['kernel/kernel.ts']})).toThrow('source mismatch'))
 test('reject reordered laws',()=>{const rows=pair();rows[1]!.laws.reverse();expect(()=>auditIntegrity(rows,source)).toThrow('different proof work')})
 test('plain controls still require equal work',()=>{const rows=pair();rows[1]!.variant='tf1-plain';for(const l of rows[1]!.laws)l.sites={};expect(auditIntegrity(rows,source)).toHaveLength(6)})
})
