// Git-only snapshot preparation; workers verify both hashes and git archive commit IDs.
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {resolve} from 'node:path'
import {type Manifest,validatePins} from './gate-evidence.ts'
const [base,cand,out='runs/mldr-incl-gates-v2']=process.argv.slice(2)
if(!base||!cand)throw Error('usage: prepare-gates.ts BASE CAND [OUTPUT_ROOT]')
const input=resolve(out,'input');mkdirSync(input,{recursive:true});const pins=[]
for(const [side,revision] of [['base',base],['cand',cand]] as const){
 const sha=execFileSync('git',['rev-parse','--verify',`${revision}^{commit}`],{encoding:'utf8'}).trim(),file=resolve(input,`${side}.tar`)
 for(const [path,pin] of [['vendor/gdp-ts','0b6ebeeec827b05210f3acfa4149a70dda9a0de5'],['vendor/handwired','d47141cce2caf5b86b0c2c0c372a5174f424bc15']] as const)if(execFileSync('git',['ls-tree',sha,path],{encoding:'utf8'}).trim().split(/\s+/)[2]!==pin)throw Error(`unsupported vendor pin: ${path}`)
 execFileSync('git',['archive','--format=tar',`--output=${file}`,sha])
 const bytes=readFileSync(file),archiveSha256=createHash('sha256').update(bytes).digest('hex')
 if(execFileSync('git',['get-tar-commit-id'],{input:bytes,encoding:'utf8'}).trim()!==sha)throw Error('archive revision mismatch')
 pins.push({sha,archiveSha256})
}
const manifest:Manifest={format:2,base:pins[0]!,cand:pins[1]!},errors=validatePins(manifest,{base:manifest.base.sha,cand:manifest.cand.sha});if(errors.length)throw Error(errors.join('; '))
for(const path of [resolve(out,'manifest.json'),resolve(input,'manifest.json')])writeFileSync(path,JSON.stringify(manifest,null,2)+'\n')
console.log(JSON.stringify({out,input,manifest}))
