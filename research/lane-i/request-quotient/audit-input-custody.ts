import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {lstatSync,mkdtempSync,readFileSync,readdirSync,readlinkSync,rmSync} from 'node:fs'
import {join} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=process.argv[2]!,temp=mkdtempSync('/tmp/quotient-custody-')
const expected={census:'7d4506ba760d1811d7bedb4de4790fe1f03ad3508688e5fdad85f16d500314e0',q1:'2433d63bf17311bf4dfa0f52fd405da99aa0e64303ebc813d873917986c020e6',types:'99d1317bff409a11191872926a4dfb03e8fcdb65099d7800c8c52ad9382a96a9'}
const hash=(data:Uint8Array|string)=>createHash('sha256').update(data).digest('hex')
function run(cmd:string,args:string[]){const r=spawnSync(cmd,args,{encoding:'utf8'});a.equal(r.status,0,r.stderr)}
function files(root:string,prefix=''):Record<string,string>{
 const out:Record<string,string>={}
 for(const name of readdirSync(join(root,prefix)).sort()){
  const path=prefix?prefix+'/'+name:name,full=join(root,path),stat=lstatSync(full)
  if(stat.isDirectory())Object.assign(out,files(root,path))
  else out[path]=stat.isSymbolicLink()?'symlink:'+readlinkSync(full):hash(readFileSync(full))
 }
 return out
}
try{
 const archives:any[]=[],inventories:Record<string,Record<string,string>>={}
 for(const [name,wanted]of Object.entries(expected)){
  const bundle=join(input,name),archive=join(bundle,'source.tar'),sha256=hash(readFileSync(archive));a.equal(sha256,wanted)
  const root=join(temp,name);run('mkdir',['-p',root]);run('tar',['-xf',archive,'-C',root]);inventories[name]=files(root)
  archives.push({name,sha256,bundleFiles:files(bundle),effectiveFiles:Object.keys(inventories[name]!).length})
 }
 a.equal(archives.find(r=>r.name==='types').bundleFiles['verify.ts'],'b17b21a86e362558430c6cbf23773ce28fb26ca011a8f99d79715f2bdfa8fe55')
 const base=inventories.census!,comparisons=['q1','types'].map(name=>{
  const next=inventories[name]!,paths=[...new Set([...Object.keys(base),...Object.keys(next)])].sort()
  const changes=paths.filter(path=>base[path]!==next[path]).map(path=>({path,before:base[path]??null,after:next[path]??null}))
  return{name,changes,unexpectedChanges:changes.filter(({path})=>!path.startsWith('research/lane-i/request-quotient/'))}
 })
 console.log('QUOTIENT_INPUT_CUSTODY '+JSON.stringify({archives,comparisons,scope:'original retained input archives; extracted last-entry-wins file inventories; no old producer rerun'}))
 for(const r of comparisons)a.equal(r.unexpectedChanges.length,0,'unexpected archive overlay: '+JSON.stringify(r.unexpectedChanges))
}finally{rmSync(temp,{recursive:true,force:true})}
