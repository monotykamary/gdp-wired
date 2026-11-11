import {strict as a} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
const dir=process.argv[2]!,repeats=Number(process.argv[3]??2)
const read=(kind:string)=>readFileSync(join(dir,`quotient-mldr-${kind}.log`),'utf8').split('\n').filter(l=>l.startsWith('QUOTIENT_MEASUREMENT ')).map(l=>JSON.parse(l.slice('QUOTIENT_MEASUREMENT '.length)))
const classes=read('classes');a.equal(classes.length,repeats)
for(const row of classes){a.equal(row.requests,36288);a.equal(row.classes,1800);a.equal(row.selector,'op');a.equal(row.quotientWorkUnits,124376)}
a.equal(classes[0].classHash,classes[1].classHash);a.deepEqual(classes[0].reads,classes[1].reads)
const reports:any[]=[]
for(const kind of['samples','generation']){
 const rows=read(kind),off=rows.filter(r=>r.quotient==='0'),on=rows.filter(r=>r.quotient==='1');a.equal(off.length,repeats);a.equal(on.length,repeats)
 const invariant=(r:any)=>kind==='samples'?r.samples:{count:r.candidateCount,hash:r.candidateHash}
 for(const r of rows)a.deepEqual(invariant(r),invariant(off[0]))
 for(const group of[off,on])for(const r of group){a.equal(r.units,group[0].units);a.deepEqual(r.raw,group[0].raw);a(r.wallMs>0)}
 a(on[0].units<off[0].units)
 const mean=(group:any[])=>group.reduce((n,r)=>n+r.wallMs,0)/group.length
 reports.push({kind,beforeWallMs:off.map(r=>r.wallMs),afterWallMs:on.map(r=>r.wallMs),beforeMeanMs:mean(off),afterMeanMs:mean(on),meanWallReduction:1-mean(on)/mean(off),beforeUnits:off[0].units,afterUnits:on[0].units,unitReduction:1-on[0].units/off[0].units,equalOutput:invariant(off[0])})
}
a(Math.abs((reports[0].beforeUnits-reports[0].afterUnits)-(reports[1].beforeUnits-reports[1].afterUnits))<1e-6,'only sampling work changed')
console.log('QUOTIENT_MEASUREMENT_AUDIT '+JSON.stringify({requestDomain:36288,classes:1800,quotientSetupUnits:124376,quotientSetupWallMs:classes.map(r=>r.quotientWallMs),reads:classes[0].reads,reports}))
