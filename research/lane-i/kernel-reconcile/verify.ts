import {strict as assert} from 'node:assert'
import {readFileSync,appendFileSync,mkdtempSync,copyFileSync,rmSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const {restore,command}=await import(resolve('recovery-input/final-gate-common.ts'))
const side=process.argv[2];assert(side==='B'||side==='F')
const pin=side==='B'?'69b8ef2b':'cd671ac1',temp=mkdtempSync('/tmp/kernel-reconcile-'),root=join(temp,'source'),input=resolve('common-kernel-input')
try{
 restore(resolve('recovery-input'),root,'b11e1f651618b3d3fcaf6cec66b4a8b0203cdcd3')
 const unpack=spawnSync('git',['unpack-objects','-q'],{cwd:root,input:readFileSync(join(input,side+'.pack'))});assert.equal(unpack.status,0)
 const commit=command('git',['rev-parse',pin],root);appendFileSync(join(root,'.git/shallow'),commit+'\n');command('git',['checkout','--detach',commit],root)
 command('bun',['install','--frozen-lockfile'],root,180000)
 const test=join(root,'lean-kernel/condition-columns.test.ts');copyFileSync(join(input,'condition-columns.test.source'),test)
 const baseline=spawnSync('bun',['test',test],{cwd:root,encoding:'utf8',timeout:120000})
 console.log('COMMON_KERNEL_BASELINE '+JSON.stringify({side,exit:baseline.status,stdout:baseline.stdout,stderr:baseline.stderr}))
 assert.equal(baseline.status,side==='B'?0:1,'F negative control must expose missing frame-only columns')
 assert(baseline.stderr.includes(side==='B'?'3 pass':'3 fail'),'all three column kinds must be exercised')
 rmSync(test)
 command('git',['apply',join(input,side+'.patch')],root)
 command('git',['add','kernel','lean-kernel'],root)
 const tree=command('git',['write-tree'],root),manifest=readFileSync(join(input,'trees.txt'),'utf8').trim().split('\n').map(l=>l.split(' ')),expected=manifest.find(row=>row[0]===side)!;assert.equal(tree,expected[1])
 const kernel=command('git',['rev-parse',tree+':kernel'],root),lean=command('git',['rev-parse',tree+':lean-kernel'],root)
 assert(manifest.every(row=>row[2]===kernel&&row[3]===lean),'one exact common kernel and Lean tree')
 copyFileSync(join(input,'condition-columns.test.source'),test)
 command('bun',['test','kernel/cdcl-root.test.ts','kernel/frame-cut.test.ts','lean-kernel/frame-export.test.ts','lean-kernel/linear-export.test.ts','core/count-frames.test.ts',test],root,300000)
 command('bun',['run','check'],root,300000)
 console.log('COMMON_KERNEL_CHECK '+JSON.stringify({passed:true,side,source:commit,tree,kernel,lean,trustedKernel:command('git',['hash-object','kernel/kernel.ts'],root),patchSha256:createHash('sha256').update(readFileSync(join(input,side+'.patch'))).digest('hex'),scope:'common-kernel overlay validation; semantic audit and integration merge remain separate'}))
}finally{rmSync(temp,{recursive:true,force:true})}
