import {expect,it} from 'bun:test'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {verifySktSource} from './skt-source-verify.ts'
const dir=process.env.SKT_CHECKED_ROOT!,checked=dir?it:it.skip
function change(file:string,replace:(s:string)=>string,check:()=>void){const old=readFileSync(file,'utf8');try{writeFileSync(file,replace(old));check()}finally{writeFileSync(file,old)}}
checked('records only conditional structural acceptance',()=>{const r=verifySktSource(dir);expect(r.status).toBe('STRUCTURAL_BRIDGE_CHECKED');expect(r.sourceSafetyChecked).toBe(false);expect(r.targetSafetyRequired).toBe(true)})
checked('refuses changed source literal',()=>{change(join(dir,'SktSourceDefs.lean'),s=>s+'\n',()=>expect(()=>verifySktSource(dir)).toThrow('source data changed'))})
checked('refuses changed actual source bytes',()=>{change(join(dir,'SktSourceOriginal.ts'),s=>s+'\n',()=>expect(()=>verifySktSource(dir)).toThrow('source data changed'))})
checked('requires the conditional public theorem',()=>{change(join(dir,'SktSourceBridge.log'),s=>s.split('\n').filter(l=>!l.includes("'skt_source_public_law_conditional'")).join('\n'),()=>expect(()=>verifySktSource(dir)).toThrow())})
checked('requires the source-derived invariant',()=>{change(join(dir,'SktSourceInvariant.log'),s=>s.split('\n').filter(l=>!l.includes("'skt_source_invariant'")).join('\n'),()=>expect(()=>verifySktSource(dir)).toThrow())})
checked('refuses a changed variable basis',()=>{change(join(dir,'SOURCE-DATA.json'),s=>{const d=JSON.parse(s);d.vars[1]='n2';return JSON.stringify(d)},()=>expect(()=>verifySktSource(dir)).toThrow('source basis changed'))})
checked('requires the frozen target identity theorem',()=>{change(join(dir,'SktSourceTarget.log'),s=>s.split('\n').filter(l=>!l.includes("'skt_target_identity'")).join('\n'),()=>expect(()=>verifySktSource(dir)).toThrow())})
checked('refuses an unconditional safety claim',()=>{change(join(dir,'SOURCE-STRUCTURAL-STATUS.json'),s=>JSON.stringify({...JSON.parse(s),sourceSafetyChecked:true}),()=>expect(()=>verifySktSource(dir)).toThrow('conditional-only'))})
