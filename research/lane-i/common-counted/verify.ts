import {strict as assert} from 'node:assert'
import {mkdtempSync,readFileSync,rmSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/common-counted-'),mode=process.argv[2]
function run(cmd:string,args:string[]){const r=spawnSync(cmd,args,{cwd:root,encoding:'utf8',timeout:1100000,maxBuffer:32*1024*1024});process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.error||r.status!==0)throw Error(`${cmd}: ${r.status} ${r.error??''}`)}
function identity(){let preserved=0;for(const line of readFileSync(join(input,'base-tree.txt'),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line)!;if(['kernel/prove.ts','kernel/cdcl.ts','kernel/epr.ts'].includes(m[2]!))continue;const b=readFileSync(join(root,m[2]!));assert.equal(createHash('sha1').update(`blob ${b.length}\0`).update(b).digest('hex'),m[1],m[2]);preserved++}
 const old=(name:string)=>readFileSync(join(input,'base-'+name),'utf8'),now=(name:string)=>readFileSync(join(root,'kernel/'+name),'utf8')
 assert.equal(now('prove.ts').split('// `units: false`')[1]!.replaceAll('traceNow()','performance.now()'),old('prove.ts').split('// `units: false`')[1])
 for(const name of ['cdcl.ts','epr.ts'])assert.equal(now(name).replace(/^import \{.* as counted(?:Trace|Search)Now\} from '[^']+'\n/gm,'').replaceAll('countedTraceNow()','performance.now()').replaceAll('countedSearchNow()','performance.now()'),old(name))
 console.log('COMMON_IDENTITY '+JSON.stringify({preserved,proverBody:'byte-identical after erasing clock calls',otherChanges:'clock calls and imports only'}))}
try{for(const name of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,name+'.tar'),'-C',root]);identity();run('bun',['install','--frozen-lockfile']);if(mode==='check')run('bun',['run','check']);else run('bun',['test','core/common-counted.test.ts','kernel/cdcl-root.test.ts','kernel/frame-cut.test.ts','lean-kernel/frame-export.test.ts','lean-kernel/linear-export.test.ts']);identity();console.log('COMMON_PORT_PASS '+JSON.stringify({mode,source:readFileSync(join(input,'source.txt'),'utf8').trim()}))}finally{rmSync(root,{recursive:true,force:true})}
