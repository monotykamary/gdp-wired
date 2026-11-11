import {cpSync,mkdtempSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
const root=mkdtempSync(join(tmpdir(),'merge-evidence-check-'))
const run=(command:string,args:string[])=>{console.log('MERGE_EVIDENCE_STAGE '+JSON.stringify({command,args}));const r=spawnSync(command,args,{cwd:root,encoding:'utf8',timeout:600000,maxBuffer:16*1024*1024});process.stdout.write(r.stdout??'');process.stderr.write(r.stderr??'');if(r.error||r.status!==0)throw Error(`${command}: ${r.status} ${r.error??''}`)}
try{
 for(const file of ['source','gdp-ts','handwired'])run('tar',['-xf',resolve('port-input',file+'.tar'),'-C',root])
 cpSync(resolve('research/lane-i/merge-0480'),join(root,'research/lane-i/merge-0480'),{recursive:true})
 run('bun',['install','--frozen-lockfile']);run(join(root,'node_modules/.bin/tsc'),['-p','.']);run(join(root,'node_modules/.bin/oxlint'),['--type-aware','--deny-warnings','--disable-nested-config'])
 console.log('MERGE_EVIDENCE_CHECK '+JSON.stringify({source:'2de2ce89f9f93eb8feb5fbfb3a355da3adafc4ef',scope:'merged production plus new evidence tooling'}))
}finally{rmSync(root,{recursive:true,force:true})}
