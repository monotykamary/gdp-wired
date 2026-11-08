import {readFileSync,readdirSync,statSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {isDeepStrictEqual} from 'node:util'
import {auditSection10Gate} from './section10-gate-audit.ts'
const [gate,diag,input,baseline]=process.argv.slice(2);if(!gate||!diag||!input||!baseline)throw new Error('GATE DIAG INPUT BASELINE required')
const json=(p:string)=>JSON.parse(readFileSync(p,'utf8')),lines=(p:string)=>readFileSync(p,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)),hash=(p:string)=>createHash('sha256').update(readFileSync(p)).digest('hex')
const byName=(a:unknown,b:unknown)=>String(a).localeCompare(String(b))
const manifest=json(join(gate,'manifest.json')),summary=json(join(gate,'summary.json')),retained=json(join(gate,'measurements.json'))
const records=['A1','B1','A2','B2','A3','B3'].map(id=>{const rs=lines(join(gate,id+'.log'));return {id,side:id[0],repeat:Number(id[1]),exitCode:retained.find((r:any)=>r.id===id)?.exitCode,laws:rs.filter(r=>r.mode==='family'),total:rs.find(r=>r.mode==='family-total')}})
if(!isDeepStrictEqual(records,retained))throw new Error('raw receipts disagree with measurements')
const audited=auditSection10Gate(records,manifest,'192ebbe2')
if(!isDeepStrictEqual(audited.laws,summary.laws)||!isDeepStrictEqual(audited.families,summary.families))throw new Error('reported table differs from raw receipts')
if(hash(input)!==manifest.inputSha256)throw new Error('input drift')
const files=(dir:string,prefix=''):string[]=>readdirSync(dir).sort(byName).flatMap(n=>statSync(join(dir,n)).isDirectory()?files(join(dir,n),prefix+n+'/'):[prefix+n])
for(const file of files('kernel'))if(hash(join('kernel',file))!==hash(join(baseline,'kernel',file)))throw new Error('kernel drift: '+file)
for(const file of ['research/track-m/profile-family.ts','package.json','bun.lock'])if(hash(file)!==hash(join(baseline,file)))throw new Error('harness or dependency drift: '+file)
for(const [file,wanted]of Object.entries(manifest.sourceHashes))if(hash(join('core',file))!==wanted)throw new Error('candidate source drift: '+file)
const profiles=lines(join(diag,'full.log')).filter(r=>r.mode==='family'),b=records.filter(r=>r.side==='B'),open=[...new Set(b.flatMap(r=>r.laws.filter((l:any)=>!l.checked).map((l:any)=>l.law)))].sort(byName)
if(JSON.stringify(profiles.filter(r=>!r.checked).map(r=>r.law).sort(byName))!==JSON.stringify(open))throw new Error('diagnostic misses an open law')
const diagnostics=readdirSync(diag).filter(n=>n.endsWith('-full.json')).map(n=>json(join(diag,n)))
if(JSON.stringify(diagnostics.map(r=>r.production.label).sort(byName))!==JSON.stringify(open))throw new Error('missing first-unfinished snapshot')
for(const r of diagnostics){if(r.revision!==manifest.candidateCommit||!r.firstUnfinished)throw new Error('diagnostic revision or path missing')}
const countMatches=profiles.every(r=>b.every(row=>{const l=row.laws.find((l:any)=>l.law===r.law);return l&&r.checked===l.checked&&Math.abs(r.countedMs-l.countedMs)<1e-6}))
console.log(JSON.stringify({audit:'section11',baseline:manifest.baselineCommit,candidate:manifest.candidateCommit,rawTablesMatch:true,noRegression:audited.noRegression,kernelEqual:manifest.kernelEqual,harnessEqual:manifest.harnessEqual,diagnosticCountsMatchEveryRepeat:countMatches,openLaws:open,laws:audited.laws,families:audited.families,laterGatesRun:false}))
