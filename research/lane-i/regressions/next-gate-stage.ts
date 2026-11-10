// File/git-only snapshot preparation; all checks and solver work run on boat.
import {readFileSync,writeFileSync,mkdirSync,readdirSync,copyFileSync,cpSync,linkSync,existsSync} from 'node:fs'
import {join,relative,resolve} from 'node:path'
import {execFileSync,spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const [stage,old,runner,outDir]=process.argv.slice(2)
if(!stage||!old||!runner)throw Error('usage: next-gate-stage.ts stage previous-data runner')
const stageRoot=stage
const git=(...args:string[])=>execFileSync('git',args,{encoding:'utf8',maxBuffer:64*1024*1024}).trim()
const hash=(v:string|Uint8Array)=>createHash('sha256').update(v).digest('hex')
const baseline=git('rev-parse','8214a543'),candidate=git('rev-parse','HEAD'),original=git('rev-parse','b788e195'),prior=git('rev-parse','d3adf3c9'),fixed=git('rev-parse','f7c5b4ba')
const refs=[original,baseline,candidate,prior,fixed]
mkdirSync(join(stage,'gate-shared-inputs'),{recursive:true});mkdirSync(join(stage,'gate-inputs'))
for(const name of ['root.pack','module-0.pack','module-1.pack'])linkSync(join(old,'gate-shared-inputs',name),join(stage,'gate-shared-inputs',name))
const objects=refs.join('\n')+'\n'+git('rev-list','--objects','--no-object-names',...refs.map(r=>r+'^{tree}'),'^'+original+'^{tree}')+'\n'
const pack=spawnSync('git',['pack-objects','--stdout','--compression=1'],{input:objects,maxBuffer:256*1024*1024})
if(pack.status!==0)throw Error(pack.stderr?.toString())
writeFileSync(join(stage,'gate-inputs/next.pack'),pack.stdout)
const priorManifest=JSON.parse(readFileSync(join(old,'gate-original-input/manifest.json'),'utf8')),revisions:Record<string,unknown>={}
for(const rev of refs){const submodules=git('ls-tree','-r',rev).split('\n').flatMap(line=>{const m=/^160000 commit ([0-9a-f]+)\t(.+)$/.exec(line);return m?[{path:m[2]!,hash:m[1]!}]:[]})
 for(const sub of submodules)if(!priorManifest.modules[sub.path]?.hashes.includes(sub.hash))throw Error('unpacked module '+sub.path)
 revisions[rev]={tree:git('rev-parse',rev+'^{tree}'),submodules}
}
const save=(p:string,v:unknown)=>writeFileSync(join(stage,p),JSON.stringify(v,null,2)+'\n')
save('gate-inputs/manifest.json',{roots:refs,rootPacks:['../gate-shared-inputs/root.pack','next.pack'],revisions,modules:priorManifest.modules})
const protectedPaths=['research/protocols/ic3syn/jobs.ts','research/protocols/ic3syn/run.ts','research/protocols/ic3syn/models.ts','research/protocols/models.ts','research/protocols/run.ts']
const paths=[...protectedPaths,'kernel/prove.ts','kernel/kernel.ts','core/counts.ts','core/solver.ts','core/laws.ts','scripts/test-shards.ts','core/effect-queue.test.ts','examples/effect-pool.ts','core/cli.ts','core/effect.ts','core/effect-prims.ts']
const source=(rev:string,ps:string[])=>Object.fromEntries(ps.map(p=>[p,hash(execFileSync('git',['show',rev+':'+p],{maxBuffer:64*1024*1024}))]))
const originalHarness=source(baseline,protectedPaths)
if(JSON.stringify(originalHarness)!==JSON.stringify(source(candidate,protectedPaths)))throw Error('canonical harness is not original')
const newTests=['core/runtime-keys.test.ts','core/sample-step.test.ts','core/small-counts.test.ts','core/cube-rows.test.ts','core/quorum-laws.test.ts','core/wall.test.ts','core/count-demand.test.ts','core/count-cert-transport.test.ts',...['conditional-check-cache','conditional-cuts','conditional-proof','derivability-closure','empty-count-source','field-bound-budget','leaf-allowance','member-inclusions','pre-state-source','rename-proof','row-demand','scalar-guards','source-witness-instances'].map(f=>'core/count-recovery/'+f+'.test.ts'),'core/extract-sol.test.ts','kernel/model-values.test.ts','scripts/test-roster.test.ts','research/lane-i/regressions/resource-run.test.ts'].map(p=>'./'+p)
for(const file of newTests)if(!existsSync(file))throw Error('missing targeted test '+file)
save('gate-inputs/gate.json',{baseline,candidate,originalHarness,sources:{base:source(baseline,paths),candidate:source(candidate,[...paths,'scripts/test-roster.ts','scripts/test-roster.test.ts','kernel/model-values.test.ts','research/lane-i/regressions/resource-run.ts','research/lane-i/regressions/next-gate-worker.ts'])},newTests})
mkdirSync(join(stage,'regression-driver/p1-tools'),{recursive:true})
for(const file of ['next-gate-worker.ts','resource-run.ts','bar-resource-pairs.ts','next-gate.jobs.json'])copyFileSync('research/lane-i/regressions/'+file,join(stage,'regression-driver',file))
copyFileSync(resolve(runner,'research/verify-all/symbolic-binder-probe.ts'),join(stage,'regression-driver/symbolic-binder-probe.ts'))
for(const file of ['lane-b-cost','audit-lane-b-cost','check-cost-profile'])copyFileSync('research/lane-i/regressions/p1-tools/'+file+'.source',join(stage,'regression-driver/p1-tools',file+'.ts'))
save('regression-driver/next-bar-roster.json',[{view:'tip',task:'tip2015/relaxedprefix_correct.smt2'}])
cpSync(join(old,'final-input'),join(stage,'evidence-input'),{recursive:true})
mkdirSync(join(stage,'integ-commits'))
for(const id of git('rev-list','--reverse',fixed+'..'+candidate).split('\n'))writeFileSync(join(stage,'integ-commits',id+'.txt'),git('show','-s','--format=%B',id)+'\n')
const hashes:Record<string,string>={}
function walk(dir:string){for(const e of readdirSync(dir,{withFileTypes:true})){const p=join(dir,e.name);if(e.isDirectory())walk(p);else hashes[relative(stageRoot,p)]=hash(readFileSync(p))}}
walk(stage)
hashes['research/verify-all/final-gate-common.ts']=hash(readFileSync(resolve(runner,'research/verify-all/final-gate-common.ts')))
save('checksums.json',hashes)
const out=outDir??'runs/lane-i/next-candidate';mkdirSync(out,{recursive:true})
writeFileSync(join(out,'input-manifest.json'),JSON.stringify({stage,baseline,candidate,manifestSha256:hash(readFileSync(join(stage,'checksums.json'))),files:hashes},null,2)+'\n')
console.log(JSON.stringify({stage,baseline,candidate,files:Object.keys(hashes).length,nextPackBytes:pack.stdout.length}))
