// File/git-only staging. The gated commit and its production files are never edited.
import{readFileSync,writeFileSync,mkdirSync,readdirSync,copyFileSync,linkSync}from'node:fs'
import{join,relative,resolve}from'node:path'
import{execFileSync,spawnSync}from'node:child_process'
import{createHash}from'node:crypto'
const[destArg,priorArg]=process.argv.slice(2);if(!destArg||!priorArg)throw Error('stage.ts destination prior-stage')
const dest=destArg,prior=priorArg,sha=(x:string|Uint8Array)=>createHash('sha256').update(x).digest('hex'),git=(...args:string[])=>execFileSync('git',args,{encoding:'utf8',maxBuffer:64*1024*1024}).trim(),candidate='a8bbe0984f270070eba9bc166a89909d0c67597e',control='97463c564351448373ca49f6af980b31b1a0f0c5',base='8214a543bc44e88d979f9e4457d7370e7e3c122b'
mkdirSync(join(dest,'gate-inputs'),{recursive:true});mkdirSync(join(dest,'gate-shared-inputs'));mkdirSync(join(dest,'driver/p1-tools'),{recursive:true})
for(const name of ['root.pack','module-0.pack','module-1.pack'])linkSync(join(prior,'gate-shared-inputs',name),join(dest,'gate-shared-inputs',name))
linkSync(join(prior,'gate-inputs/next.pack'),join(dest,'gate-inputs/next.pack'))
const manifest=JSON.parse(readFileSync(join(prior,'gate-inputs/manifest.json'),'utf8'));if(!manifest.revisions[candidate]||!manifest.revisions[base])throw Error('prior stage lacks frozen candidate/base')
const objects=control+'\n'+git('rev-list','--objects','--no-object-names',control+'^{tree}',...manifest.roots.map((r:string)=>'^'+r+'^{tree}'))+'\n',pack=spawnSync('git',['pack-objects','--stdout','--compression=1'],{input:objects,maxBuffer:256*1024*1024});if(pack.status!==0)throw Error(pack.stderr?.toString());writeFileSync(join(dest,'gate-inputs/control.pack'),pack.stdout)
manifest.roots.push(control);manifest.rootPacks.push('control.pack');manifest.revisions[control]={tree:git('rev-parse',control+'^{tree}'),submodules:git('ls-tree','-r',control).split('\n').flatMap(line=>{const m=/^160000 commit ([0-9a-f]+)\t(.+)$/.exec(line);return m?[{path:m[2]!,hash:m[1]!}]:[]})}
for(const sub of manifest.revisions[control].submodules)if(!manifest.modules[sub.path]?.hashes.includes(sub.hash))throw Error('unsupported submodule')
const save=(p:string,v:unknown)=>writeFileSync(join(dest,p),JSON.stringify(v,null,2)+'\n');save('gate-inputs/manifest.json',manifest)
const paths=['core/counts.ts','kernel/prove.ts','kernel/kernel.ts','core/solver.ts','core/laws.ts','core/effect-queue.test.ts','examples/effect-pool.ts','core/effect.ts','core/effect-prims.ts'],revisions={base,control,candidate},sources=Object.fromEntries(Object.entries(revisions).map(([side,rev])=>[side,Object.fromEntries(paths.map(p=>[p,sha(execFileSync('git',['show',rev+':'+p]))]))]))
const family='/private/tmp/lane-i-p1-final-data.LXblGC/final-input/family.json';copyFileSync(family,join(dest,'family.json'));const familySha256=sha(readFileSync(family));if(familySha256!=='5dbdbf766e9949b051d0764920f1bcc3707690cd6852fca6d0bcf18674fbdac4')throw Error('wrong original p1 family')
const oldHashes=JSON.parse(readFileSync('/private/tmp/lane-i-p1-final-data.LXblGC/checksums.json','utf8'))
for(const f of ['lane-b-cost','audit-lane-b-cost','check-cost-profile']){const source='research/lane-i/regressions/p1-tools/'+f+'.source',out='driver/p1-tools/'+f+'.ts';if(sha(readFileSync(source))!==oldHashes['regression-driver/p1-tools/'+f+'.ts'])throw Error('original helper changed '+f);copyFileSync(source,join(dest,out))}
copyFileSync('research/lane-i/follow-up/gated-follow-up.ts',join(dest,'driver/gated-follow-up.ts'));copyFileSync('research/lane-i/regressions/resource-run.ts',join(dest,'driver/resource-run.ts'))
if(sources.base!['core/effect-queue.test.ts']!==sources.candidate!['core/effect-queue.test.ts'])throw Error('effect test differs')
save('config.json',{revisions,sources,familySha256,effectTestSha256:sources.base!['core/effect-queue.test.ts'],gatedTree:git('rev-parse',candidate+'^{tree}'),expectedCandidateCounts:'7a4c830848afa2d05393bdd00c546393092cf1f94d5ce9cdee8a2aad9189abd4',notes:'core/laws differs in optional-source parsing; p1 input is the unchanged serialized native family'})
const hashes:Record<string,string>={};function walk(dir:string){for(const e of readdirSync(dir,{withFileTypes:true})){const p=join(dir,e.name);if(e.isDirectory())walk(p);else hashes[relative(dest,p)]=sha(readFileSync(p))}}walk(dest)
hashes['research/verify-all/final-gate-common.ts']=sha(readFileSync('/private/tmp/lane-i-paxos-runner.djtUt9/research/verify-all/final-gate-common.ts'));save('checksums.json',hashes)
const out=resolve('runs/lane-i/gated-follow-up');mkdirSync(out,{recursive:true});writeFileSync(join(out,'input-manifest.json'),JSON.stringify({stage:dest,revisions,gatedTree:git('rev-parse',candidate+'^{tree}'),manifestSha256:sha(readFileSync(join(dest,'checksums.json'))),files:hashes},null,2)+'\n');console.log(JSON.stringify({stage:dest,revisions,controlPackBytes:pack.stdout.length,files:Object.keys(hashes).length}))
