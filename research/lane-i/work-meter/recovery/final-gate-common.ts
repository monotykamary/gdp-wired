import {readFileSync,writeFileSync,mkdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {join,resolve} from 'node:path'
import {createHash} from 'node:crypto'
export const sha=(s:string|Uint8Array)=>createHash('sha256').update(s).digest('hex')
export const readJson=(p:string):any=>JSON.parse(readFileSync(p,'utf8'))
export function command(cmd:string,args:string[],cwd=process.cwd(),timeout=120000){const p=spawnSync(cmd,args,{cwd,encoding:'utf8',timeout,maxBuffer:128*1024*1024});if(p.status!==0)throw Error(`${cmd} ${args.join(' ')}: ${p.stderr}\n${p.stdout}`);return p.stdout.trim()}
export const git=(args:string[],cwd=process.cwd())=>command('git',args,cwd)
export const save=(p:string,x:unknown)=>writeFileSync(p,JSON.stringify(x,null,2)+'\n')
export function snapshot(input:string,revisions:string[]){
 mkdirSync(input,{recursive:true});const roots=[...new Set(revisions)],manifest:any={revisions:{},modules:{},roots}
 const objects=(rev:string,cwd:string)=>rev+'\n'+git(['rev-list','--objects','--no-object-names',`${rev}^{tree}`],cwd)+'\n'
 const pack=(file:string,text:string,cwd:string)=>{const p=spawnSync('git',['pack-objects','--stdout'],{cwd,input:text,timeout:120000,maxBuffer:128*1024*1024});if(p.status!==0)throw Error(p.stderr.toString());writeFileSync(join(input,file),p.stdout)}
 pack('root.pack',roots.map(r=>objects(r,process.cwd())).join(''),process.cwd())
 const modules=new Map<string,Set<string>>()
 for(const rev of roots){const submodules=git(['ls-tree','-r',rev]).split('\n').flatMap(line=>{const m=line.match(/^160000 commit ([0-9a-f]+)\t(.+)$/);if(!m)return[];const path=m[2]!,hash=m[1]!;if(!modules.has(path))modules.set(path,new Set());modules.get(path)!.add(hash);return[{path,hash}]});manifest.revisions[rev]={tree:git(['rev-parse',`${rev}^{tree}`]),submodules}}
 let n=0;for(const [path,hashes]of modules){const file=`module-${n++}.pack`,cwd=resolve(path);pack(file,[...hashes].map(h=>objects(h,cwd)).join(''),cwd);manifest.modules[path]={file,hashes:[...hashes]}}
 save(join(input,'manifest.json'),manifest);return manifest
}
export function restore(input:string,dest:string,rev:string){
 const m=readJson(join(input,'manifest.json')),r=m.revisions[rev];if(!r)throw Error('snapshot lacks revision '+rev)
 const unpack=(path:string,file:string,heads:string[])=>{mkdirSync(path,{recursive:true});git(['init','-q'],path);const p=spawnSync('git',['unpack-objects','-q'],{cwd:path,input:readFileSync(join(input,file)),timeout:120000});if(p.status!==0)throw Error(p.stderr?.toString());writeFileSync(join(path,'.git/shallow'),heads.join('\n')+'\n')}
 unpack(dest,(m.rootPacks??['root.pack'])[0],m.roots);for(const file of (m.rootPacks??[]).slice(1)){const p=spawnSync('git',['unpack-objects','-q'],{cwd:dest,input:readFileSync(join(input,file)),timeout:120000});if(p.status!==0)throw Error(p.stderr?.toString())}git(['-c','advice.detachedHead=false','checkout','-q','--detach',rev],dest)
 for(const sub of r.submodules){const sm=m.modules[sub.path],path=join(dest,sub.path);unpack(path,sm.file,sm.hashes);git(['-c','advice.detachedHead=false','checkout','-q','--detach',sub.hash],path)}
 git(['submodule','init'],dest);git(['submodule','absorbgitdirs'],dest)
 const dirty=git(['status','--porcelain','--untracked-files=all'],dest);if(dirty)throw Error('unclean snapshot '+dirty)
 if(git(['rev-parse','HEAD'],dest)!==rev||git(['rev-parse','HEAD^{tree}'],dest)!==r.tree)throw Error('snapshot identity mismatch')
 return {revision:rev,tree:r.tree,submodules:git(['submodule','status','--recursive'],dest),clean:true}
}
export const protectedHarness=['research/protocols/ic3syn/jobs.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts','research/protocols/models.ts','research/protocols/run.ts']
export function harnessHashes(dir:string){return Object.fromEntries(protectedHarness.map(p=>[p,sha(readFileSync(join(dir,p)))]))}
if(import.meta.main){const [input,base,cand]=process.argv.slice(2);if(!input||!base||!cand)throw Error('usage: final-gate-common.ts input base candidate');const baseline=git(['rev-parse',base+'^{commit}']),candidate=git(['rev-parse',cand+'^{commit}']);snapshot(input,[baseline,candidate]);save(join(input,'gate.json'),{baseline,candidate})}
