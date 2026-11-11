import {strict as a} from 'node:assert'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
const [dir,source]=process.argv.slice(2),file='quotient-mldr-9950x-abba'
const placement=JSON.parse(readFileSync(join(dir!,'placement.json'),'utf8'))[file]
a(placement);a.equal(placement.type,'xlarge');a.equal(placement.cpu,'AMD Ryzen 9 9950X 16-Core Processor');a.equal(placement.exclusive,true);a.equal(placement.co_tenants,0);a.equal(placement.vcpus,8);a.equal(placement.vm_vcpus,16)
const lines=readFileSync(join(dir!,file+'.log'),'utf8').split('\n')
const contexts=lines.filter(l=>l.startsWith('QUOTIENT_MEASUREMENT_CONTEXT ')).map(l=>JSON.parse(l.slice('QUOTIENT_MEASUREMENT_CONTEXT '.length)))
for(const c of contexts)a.equal(c.source,source)
const all=lines.filter(l=>l.startsWith('QUOTIENT_MEASUREMENT ')).map(l=>JSON.parse(l.slice('QUOTIENT_MEASUREMENT '.length)))
a.equal(all.length,10);for(const r of all){a.equal(r.proofQueries,0);a.equal(r.callerCount,4);a.equal(r.scope,'real-admission-prefix-with-kind-laws')}
const classes=all.filter(r=>r.kind==='classes');a.equal(classes.length,2)
for(const row of classes){a.equal(row.requests,36288);a.equal(row.classes,1800);a.equal(row.selector,'op');a.equal(row.quotientWorkUnits,124376)}
a.equal(classes[0].classHash,classes[1].classHash);a.deepEqual(classes[0].reads,classes[1].reads)
const reports:any[]=[]
for(const kind of['samples','generation']){
 const rows=all.filter(r=>r.kind===kind);a.deepEqual(rows.map(r=>r.quotient),['0','1','1','0'])
 const off=rows.filter(r=>r.quotient==='0'),on=rows.filter(r=>r.quotient==='1')
 const output=(r:any)=>kind==='samples'?r.samples:{count:r.candidateCount,hash:r.candidateHash}
 for(const r of rows)a.deepEqual(output(r),output(off[0]))
 for(const group of[off,on])for(const r of group){a.equal(r.units,group[0].units);a.deepEqual(r.raw,group[0].raw);a(r.wallMs>0)}
 a(on[0].units<off[0].units)
 const mean=(group:any[])=>group.reduce((n,r)=>n+r.wallMs,0)/group.length
 reports.push({kind,order:'ABBA',beforeWallMs:off.map(r=>r.wallMs),afterWallMs:on.map(r=>r.wallMs),beforeMeanMs:mean(off),afterMeanMs:mean(on),meanWallReduction:1-mean(on)/mean(off),beforeUnits:off[0].units,afterUnits:on[0].units,unitReduction:1-on[0].units/off[0].units,equalOutput:output(off[0])})
}
a.equal(reports[1].equalOutput.count,43)
a(Math.abs((reports[0].beforeUnits-reports[0].afterUnits)-(reports[1].beforeUnits-reports[1].afterUnits))<1e-6)
console.log('QUOTIENT_PINNED_TIMING_AUDIT '+JSON.stringify({source,placement,requestDomain:36288,classes:1800,quotientSetupUnits:124376,quotientSetupWallMs:classes.map(r=>r.quotientWallMs),reads:classes[0].reads,proofQueries:0,reports,scope:'current integrated source only; not a timing of the older 49-law lane-B tree, and not an end-to-end 60s proof'}))
