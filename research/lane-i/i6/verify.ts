import {strict as assert} from 'node:assert'
import {mkdtempSync,readFileSync,rmSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/i6-source-'),base=mkdtempSync('/tmp/i6-base-'),mode=process.argv[2]
function run(cmd:string,args:string[],cwd=root){const r=spawnSync(cmd,args,{cwd,encoding:'utf8',timeout:1100000,maxBuffer:32*1024*1024});process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.error||r.status!==0)throw Error(`${cmd}: ${r.status} ${r.error??''}`)}
function identity(){let preserved=0;for(const line of readFileSync(join(input,'frozen-tree.txt'),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line)!;if(['kernel/prove.ts','kernel/kernel.ts','core/check.ts'].includes(m[2]!))continue;const b=readFileSync(join(root,m[2]!));assert.equal(createHash('sha1').update(`blob ${b.length}\0`).update(b).digest('hex'),m[1],m[2]!);preserved++}
 const body=(s:string)=>s.slice(s.indexOf('// `units: false`'));assert.equal(body(readFileSync(join(root,'kernel/prove.ts'),'utf8')),body(readFileSync(join(input,'base-prove.ts'),'utf8')));console.log('I6_PROTECTED_IDENTITIES '+JSON.stringify({preserved,changed:['kernel/kernel.ts','core/check.ts'],proverBody:'unchanged'}))}
try{
 run('tar',['-xf',join(input,'baseline.tar'),'-C',base]);for(const name of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,name+'.tar'),'-C',root]);identity();run('bun',['install','--frozen-lockfile']);run('bun',['research/lane-i/i6/identity.ts',base,root]);
 if(mode==='check')run('bun',['run','check']);else run('bun',['test','core/i6-meter.test.ts','core/work-admission-perf.test.ts','core/work-observe.test.ts','core/hard-cap.test.ts','core/common-counted.test.ts','core/check.test.ts','kernel/count.test.ts','kernel/countmachine.test.ts','kernel/cdcl-root.test.ts','kernel/frame-cut.test.ts','lean-kernel/frame-export.test.ts','lean-kernel/linear-export.test.ts']);identity();console.log('I6_GATE '+JSON.stringify({mode,source:readFileSync(join(input,'source.txt'),'utf8').trim()}))
}finally{rmSync(root,{recursive:true,force:true});rmSync(base,{recursive:true,force:true})}
