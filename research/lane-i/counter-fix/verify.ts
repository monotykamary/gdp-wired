import {strict as assert} from 'node:assert'
import {mkdtempSync,readFileSync,rmSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/hard-cap-'),mode=process.argv[2]
function run(cmd:string,args:string[]){const r=spawnSync(cmd,args,{cwd:root,encoding:'utf8',timeout:1100000,maxBuffer:32*1024*1024});process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.error||r.status!==0)throw Error(`${cmd}: ${r.status} ${r.error??''}`)}
function identity(){let preserved=0;for(const line of readFileSync(join(input,'frozen-tree.txt'),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line)!;if(m[2]==='kernel/prove.ts')continue;const b=readFileSync(join(root,m[2]!));assert.equal(createHash('sha1').update(`blob ${b.length}\0`).update(b).digest('hex'),m[1],m[2]!);preserved++}
 const body=(s:string)=>s.slice(s.indexOf('// `units: false`'))
 assert.equal(body(readFileSync(join(root,'kernel/prove.ts'),'utf8')),body(readFileSync(join(input,'base-prove.ts'),'utf8')))
 console.log('FROZEN_CHECKING '+JSON.stringify({preserved,proverBody:'exact below cancellation header'}))}
try{
 for(const name of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,(name==='source'&&mode==='negative'?'baseline':name)+'.tar'),'-C',root])
 identity();run('bun',['install','--frozen-lockfile'])
 if(mode==='negative'){
  writeFileSync(join(root,'core/hard-cap.test.ts'),readFileSync(join(input,'guard-test.ts')))
  const r=spawnSync('bun',['test','core/hard-cap.test.ts'],{cwd:root,encoding:'utf8',timeout:120000,maxBuffer:8*1024*1024})
  process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');assert(!r.error);assert.notEqual(r.status,0);assert((r.stderr??'').includes('counted binding loops'))
  console.log('BASELINE_GUARD_REJECTED')
 }else if(mode==='check')run('bun',['run','check'])
 else run('bun',['test','core/work-observe.test.ts','core/hard-cap.test.ts','core/common-counted.test.ts','kernel/cdcl-root.test.ts','kernel/frame-cut.test.ts','lean-kernel/frame-export.test.ts','lean-kernel/linear-export.test.ts'])
 identity();console.log('HARD_CAP_GATE '+JSON.stringify({mode,source:readFileSync(join(input,'source.txt'),'utf8').trim()}))
}finally{rmSync(root,{recursive:true,force:true})}
