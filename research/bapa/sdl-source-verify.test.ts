import {expect,it} from 'bun:test'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {verifySdlSource} from './sdl-source-verify.ts'
const dir=process.env.SDL_CHECKED_ROOT!,deps=process.env.SDL_DEPENDENCY_ROOT!
const checked=dir&&deps?it:it.skip
function change(file:string,replace:(s:string)=>string,check:()=>void){const old=readFileSync(file,'utf8');try{writeFileSync(file,replace(old));check()}finally{writeFileSync(file,old)}}
checked('requires the whole SDL family, exact sums and original source theorem',()=>{expect(verifySdlSource(dir,deps).status).toBe('SOURCE_CHECKED')})
checked('refuses a modified source definition',()=>{change(join(dir,'SdlSourceDefs.lean'),s=>s+'\n',()=>expect(()=>verifySdlSource(dir,deps)).toThrow('source data changed'))})
checked('refuses absent source theorem output',()=>{change(join(dir,'SdlSourceBridge.log'),s=>s.split('\n').filter(l=>!l.includes("'bapa_simple_decentralized_lock_source_law'")).join('\n'),()=>expect(()=>verifySdlSource(dir,deps)).toThrow())})
checked('refuses absent exact SUM cover theorem output',()=>{change(join(deps,'SumChecks.log'),s=>s.split('\n').filter(l=>!l.includes("'Bapa.SdlConcrete.Checked.cover'")).join('\n'),()=>expect(()=>verifySdlSource(dir,deps)).toThrow())})
