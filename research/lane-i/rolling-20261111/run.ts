import {strict as a} from 'node:assert'
import {createHash} from 'node:crypto'
import {readFileSync,mkdtempSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
const input=resolve('port-input'),root=mkdtempSync('/tmp/rolling-integration-'),[mode,...files]=process.argv.slice(2)
function run(command:string,args:string[]){const p=spawnSync(command,args,{cwd:root,env:process.env,encoding:'utf8',timeout:800000,maxBuffer:64*1024*1024});process.stdout.write(p.stdout??'');process.stderr.write(p.stderr??'');if(p.error||p.status!==0)throw Error(`${command} failed (${p.status}): ${p.error??''}`)}
function identities(){let checked=0;for(const line of readFileSync(join(input,'PROTECTED.tree'),'utf8').trim().split('\n')){const m=/^\d+ blob ([a-f0-9]+)\t(.+)$/.exec(line);a(m);const bytes=readFileSync(join(root,m[2]!));a.equal(createHash('sha1').update(`blob ${bytes.length}\0`).update(bytes).digest('hex'),m[1],m[2]!);checked++}return checked}
try{
 for(const name of ['source','gdp-ts','handwired'])run('tar',['-xf',join(input,name+'.tar'),'-C',root])
 const before=identities();run('bun',['install','--frozen-lockfile'])
 if(mode==='types')run('bun',['run','check']);else if(mode==='test')run('bun',['test',...files]);else throw Error('unknown mode '+mode)
 a.equal(identities(),before)
 console.log('ROLLING_GATE '+JSON.stringify({sourceTree:readFileSync(join(input,'source.txt'),'utf8').trim(),mode,files,protected:before}))
}finally{rmSync(root,{recursive:true,force:true})}
