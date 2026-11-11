import {strict as assert} from 'node:assert'
import {createHash} from 'node:crypto'
import {closeSync,mkdirSync,mkdtempSync,openSync,readFileSync,rmSync,statSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),source=readFileSync(join(input,'source.txt'),'utf8').trim(),root=mkdtempSync('/tmp/strict-originals-unit-')
const out=resolve('/home/user/.sc-artifacts/lane-i-strict-originals',source,'unit')
const profile=JSON.parse(readFileSync(join(input,'flags.json'),'utf8')),off={GDP_WORK_FULL:'0',GDP_WORK_STEPS:'0'}
const clean=Object.fromEntries(Object.entries(process.env).filter(([key])=>!key.startsWith('GDP_')))
mkdirSync(out,{recursive:true})
const hash=(bytes:Buffer)=>createHash('sha256').update(bytes).digest('hex')
const blob=(bytes:Buffer)=>createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex')
const files:any[]=[]
function run(label:string,cmd:string,args:string[],flags:Record<string,string>=profile){const path=join(out,label+'.log'),fd=openSync(path,'w');const r=spawnSync(cmd,args,{cwd:root,env:{...clean,...flags},stdio:['ignore',fd,fd],timeout:300000});closeSync(fd);const row={path,bytes:statSync(path).size,sha256:hash(readFileSync(path)),exit:r.status};files.push(row);console.log('UNIT_FILE '+JSON.stringify(row));assert.equal(r.status,0,label)}
function identities(){const lines=readFileSync(join(input,'PROTECTED.tree'),'utf8').trim().split('\n');assert.equal(lines.length,181);for(const line of lines){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);assert(m);assert.equal(blob(readFileSync(join(root,m[2]!))),m[1],m[2]!)}}
try{
 for(const line of readFileSync(join(input,'SHA256SUMS'),'utf8').trim().split('\n')){const m=/^([a-f0-9]{64})  ([a-z-]+\.tar)$/.exec(line);assert(m);assert.equal(hash(readFileSync(join(input,m[2]!))),m[1])}
 for(const name of ['source','gdp-ts','handwired'])run('extract-'+name,'tar',['-xf',join(input,name+'.tar'),'-C',root])
 identities();run('install','bun',['install','--frozen-lockfile'])
 const tests=['core/evaluation-admission.test.ts','core/prover-row-admission.test.ts','core/table-admission.test.ts','core/count-admission.test.ts','core/work-admission-perf.test.ts']
 run('admission-full','bun',['test',...tests]);run('admission-off','bun',['test',...tests],off)
 run('typecheck','bunx',['tsc','--noEmit']);run('lint','bunx',['oxlint','--type-aware','--deny-warnings','--disable-nested-config'])
 identities();writeFileSync(join(out,'summary.json'),JSON.stringify({source,status:'PASS',protectedFiles:181,files},null,2)+'\n');console.log('UNIT_PASS '+source)
}catch(error){console.log('UNIT_FAILURE '+JSON.stringify({source,out,error:String(error)}));writeFileSync(join(out,'failure.json'),JSON.stringify({source,error:String(error),files},null,2)+'\n');process.exitCode=1}finally{rmSync(root,{recursive:true,force:true})}
