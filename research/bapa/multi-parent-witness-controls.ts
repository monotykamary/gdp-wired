// Negative custody controls against an actual successfully built project.
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {verifyWitnessSourceProject} from './witness-source-verify.ts'
const [directory,logfile]=process.argv.slice(2)
if(!directory||!logfile)throw Error('project and completed log required')
const log=readFileSync(logfile,'utf8'),r=JSON.parse(readFileSync(join(directory,'EMITTED.json'),'utf8'))
const paths=r.sourceProjection?.parentPaths
if(!Array.isArray(paths)||paths.length!==2)throw Error('expected two retained parent paths')
verifyWitnessSourceProject(directory,log)
for(const p of paths){
 const name=p.sourceTheorems[0]
 const missing=log.split('\n').filter(line=>!line.includes("'"+name+"'")).join('\n')
 let refused=false
 try{verifyWitnessSourceProject(directory,missing)}catch(error){refused=String(error).includes('missing exact theorem axiom output: '+name)}
 if(!refused)throw Error('missing path theorem was accepted: '+name)
}
console.log(JSON.stringify({positive:true,missingParentTheoremsRefused:paths.length}))
