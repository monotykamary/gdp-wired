// Acceptance requires an exact independent roster and both explicitly requested revisions.
import {readFileSync,readdirSync,writeFileSync} from 'node:fs'
import {auditSuite,SUITES,type Manifest,type Suite} from './gate-evidence.ts'
const [root,base,cand,scope]=process.argv.slice(2)
if(!root||!base||!cand)throw Error('usage: analyze-gates.ts ROOT BASE_FULL_SHA CAND_FULL_SHA [ic3syn,duoai,broken]')
const kinds=(scope?.split(',')??SUITES) as Suite[]
if(new Set(kinds).size!==kinds.length||kinds.some(k=>!SUITES.includes(k)))throw Error('invalid analysis scope')
const manifest=JSON.parse(readFileSync(`${root}/manifest.json`,'utf8')) as Manifest
const suites=Object.fromEntries(kinds.map(kind=>{const dir=`${root}/${kind}`,logs=Object.fromEntries(readdirSync(dir).filter(f=>f.endsWith('.log')).map(f=>[f,readFileSync(`${dir}/${f}`,'utf8')])),receipts=readFileSync(`${dir}/summary.tsv`,'utf8');return [kind,auditSuite(kind,{logs,receipts},manifest,{base,cand})]}))
const complete=kinds.length===SUITES.length,componentPass=Object.values(suites).every(s=>s.pass),out={format:2,base,cand,complete,scope:kinds,pass:complete&&componentPass,componentPass,suites}
writeFileSync(`${root}/verdicts-v2${complete?'':'-'+kinds.join('-')}.json`,JSON.stringify(out,null,2)+'\n')
console.log(JSON.stringify({...out,suites:Object.fromEntries(Object.entries(suites).map(([key,suite])=>[key,{...suite,rows:undefined}]))}))
if(!componentPass)process.exitCode=1
