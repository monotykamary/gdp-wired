// T-F4 only: exact untrusted copy of the current row assembler, not a kernel edit.
import {readFileSync,writeFileSync} from 'node:fs'
import ts from 'typescript'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const kernel=readFileSync('kernel/kernel.ts','utf8'),ast=ts.createSourceFile('kernel.ts',kernel,ts.ScriptTarget.Latest,true)
const functions=['decide','sameKey','leafRows'].map(name=>{const fn=ast.statements.find((n):n is ts.FunctionDeclaration=>ts.isFunctionDeclaration(n)&&n.name?.text===name);if(!fn)throw new Error('missing row function '+name);return fn.getText(ast)})
const file='research/track-m/section8-incremental-rows.ts';let s=readFileSync(file,'utf8')
const marker='const buildRows=(goal:Goal,path:Path,_factsOf:(h:C)=>Lin[])=>leafConstraintsReusing(goal,path)'
if(s.split(marker).length!==2)throw new Error('missing row assembly marker')
s="import {type Constraint,scale,sub,v} from '../../core/solver.ts'\nimport {atomOf,canonFlip,isCell,cellParts,termRows} from '../../kernel/kernel.ts'\nconst look=(path:Path,key:string)=>path.get(key)?.holds\n"+s.replace(marker,'const buildRows=leafRows')+'\n'+functions.join('\n')+'\n'
writeFileSync(file,s)
const cache='kernel/prover-rows.ts',before=readFileSync(cache,'utf8'),call='out=leafConstraintsReusing(shared,path)'
if(before.split(call).length!==2)throw new Error('missing prover row miss')
writeFileSync(cache,"import {incrementalRows} from '../research/track-m/section8-incremental-rows.ts'\n"+before.replace(call,'out=incrementalRows(shared,path)').replace('canon,leafConstraintsReusing','canon'))
const runner='research/track-m/run-phase-census.ts';writeFileSync(runner,readFileSync(runner,'utf8')+"\nconsole.log(JSON.stringify({test:'T-F4-stats',...(await import('./section8-incremental-rows.ts')).incrementalStats}))\n")
console.log(JSON.stringify({installed:'T-F4',trustedKernelChanged:false,retentionCap:4096,rowWeightCap:250000}))
