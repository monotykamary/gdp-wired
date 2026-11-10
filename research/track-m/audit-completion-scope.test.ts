import {test,expect} from 'bun:test'
import {auditCompletionLog} from './audit-completion-scope.ts'
const hash='a'.repeat(64),identity={beforeSha256:hash,afterSha256:hash,gateBase:'base'}
const commonHashes=Object.fromEntries(['core/machine.ts','core/dsl.ts','core/solver.ts','kernel/kernel.ts','kernel/prove.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts'].map(p=>[p,hash]))
function fixture(mode:'strict'|'census'){
 const outcome=mode==='census'?{count:1,canonicalSha256:hash,namesSha256:hash}:{exit:0,result:{id:'consensus_forall',search:{verdict:'proven',full:1,work:2}},namesSha256:hash}
 const rows=Array.from({length:mode==='strict'?5:3},(_,i)=>({repeat:i+1,order:(i+2)%2?['after','before']:['before','after'],outcomes:{before:structuredClone(outcome),after:structuredClone(outcome)}}))
 const done={records:rows.length,meta:{identity,mode,model:'example',cohort:1,cpu:'AMD Ryzen 9 9950X 16-Core Processor',strictMs:mode==='strict'?60000:null,source:{before:hash,after:hash},gateBase:'base',focusDisabled:false,newProcesses:true,commonHashes}}
 return {rows,done,text:()=>rows.map(r=>'COMPLETION_SCOPE_REPEAT '+JSON.stringify(r)).join('\n')+'\nCOMPLETION_SCOPE_DONE '+JSON.stringify(done)}
}
test('census requires three unique complete source-bound matching pairs',()=>{
 const f=fixture('census');expect(auditCompletionLog(f.text(),'census',identity,'example').pairs).toBe(3)
 f.rows.pop();expect(()=>auditCompletionLog(f.text(),'census',identity,'example')).toThrow()
})
test('mismatched laws, source identity, or terminal cardinality are rejected',()=>{
 const f=fixture('census');f.rows[0]!.outcomes.after.namesSha256='b'.repeat(64);expect(()=>auditCompletionLog(f.text(),'census',identity,'example')).toThrow()
 const g=fixture('census');g.done.meta.source.after='b'.repeat(64);expect(()=>auditCompletionLog(g.text(),'census',identity,'example')).toThrow()
 const h=fixture('census');expect(()=>auditCompletionLog(h.text()+'\nCOMPLETION_SCOPE_DONE '+JSON.stringify(h.done),'census',identity,'example')).toThrow()
})
test('strict repeats require the right CPU; censored results are not counted as proofs',()=>{
 const f=fixture('strict');expect(auditCompletionLog(f.text(),'strict',identity).provenPairs).toBe(5)
 Object.assign(f.rows[0]!.outcomes.after,{exit:null,result:null})
 const r=auditCompletionLog(f.text(),'strict',identity);expect(r.provenPairs).toBe(4);expect(r.pairs).toBe(4);expect(r.verdictLosses).toBe(1)
 f.done.meta.cpu='other';expect(()=>auditCompletionLog(f.text(),'strict',identity)).toThrow()
})
test('a CPU skip is zero accepted pairs, never a complete run',()=>{
 expect(auditCompletionLog('COMPLETION_CPU_SKIP {"cpu":"other"}','strict',identity).pairs).toBe(0)
 expect(()=>auditCompletionLog('COMPLETION_CPU_SKIP {"cpu":"AMD Ryzen 9 9950X 16-Core Processor"}','strict',identity)).toThrow()
})
