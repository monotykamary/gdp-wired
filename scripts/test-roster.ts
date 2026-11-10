import {readdirSync} from 'node:fs'
import {join,posix} from 'node:path'
const scoped=(p:string)=>p.startsWith('core/')||p.startsWith('kernel/')
export function coreKernelTests(root:string):string[]{
 const files:string[]=[]
 function walk(dir:string){for(const e of readdirSync(join(root,dir),{withFileTypes:true})){const p=dir+'/'+e.name;if(e.isDirectory())walk(p);else if(e.isFile()&&p.endsWith('.test.ts'))files.push(p)}}
 walk('core');walk('kernel');return files.sort()
}
// Read only literal test paths from the checked-in long-suite shell commands.
// Unknown/dynamic spellings cover nothing, so new files cannot silently disappear.
export function longSuiteTests(jobs:{cwd?:string,cmd:string}[]):string[]{
 const files=new Set<string>()
 for(const job of jobs){let cwd=job.cwd??'.'
  for(const m of job.cmd.matchAll(/(?:^|&&|;)\s*(?:[A-Za-z_]\w*=[\w./:-]+\s+)*(?:cd\s+([\w./-]+)|bun\s+test\s+([^;&]+))/g)){
   if(m[1]){cwd=posix.normalize(posix.join(cwd,m[1]));continue}
   for(const token of (m[2]??'').trim().split(/\s+/))if(/^(?:\.\/)?[\w./-]+\.test\.ts$/.test(token)){
    const file=posix.normalize(posix.join(cwd,token));if(scoped(file))files.add(file)
   }
  }
 }
 return [...files].sort()
}
export function auditTestRoster(files:readonly string[],quick:readonly string[],long:readonly string[]){
 const actual=new Set(files),listed=quick.filter(scoped),covered=new Set([...listed,...long]),seen=new Set<string>(),duplicates:string[]=[]
 for(const p of listed){if(seen.has(p))duplicates.push(p);seen.add(p)}
 return{missing:files.filter(p=>!covered.has(p)).sort(),nonexistent:[...covered].filter(p=>scoped(p)&&!actual.has(p)).sort(),duplicates:[...new Set(duplicates)].sort()}
}
export function assertTestRoster(files:readonly string[],quick:readonly string[],long:readonly string[]):void{
 const result=auditTestRoster(files,quick,long)
 if(Object.values(result).some(xs=>xs.length))throw Error('core/kernel test roster incomplete: '+JSON.stringify(result))
}
