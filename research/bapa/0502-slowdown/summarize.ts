import {readFileSync, writeFileSync} from 'node:fs'

type Row = {label:string, head:string, phase:string, case:string, direct?:{ioWriteMs:number,checkWallMs:number,lawMs:number,loweringRenamingResidualMs:number,binder?:Record<string,number>}, whole?:{processWallMs:number,testMs?:number,status:number}}
const [input, output] = process.argv.slice(2)
if (!input || !output) throw Error('usage: bun summarize.ts observations.jsonl SUMMARY.json')
const rows = readFileSync(input, 'utf8').trim().split('\n').filter(Boolean).map(line => JSON.parse(line) as Row)
const median = (xs:number[]) => [...xs].sort((a,b)=>a-b)[Math.floor(xs.length / 2)]!
const mean = (xs:number[]) => xs.reduce((a,b)=>a+b,0) / xs.length
const sd = (xs:number[]) => { const m=mean(xs); return Math.sqrt(xs.reduce((a,b)=>a+(b-m)**2,0)/(xs.length-1)) }
const metric = (r:Row, name:string):number|undefined => name === 'lawMs' ? r.direct?.lawMs : name === 'checkWallMs' ? r.direct?.checkWallMs : name === 'loweringRenamingResidualMs' ? r.direct?.loweringRenamingResidualMs : name === 'ioWriteMs' ? r.direct?.ioWriteMs : name === 'testMs' ? r.whole?.testMs : name === 'processWallMs' ? r.whole?.processWallMs : undefined
const commits = {r70:'70b660443', c149:'c149b540', c96:'96bf476', c08:'c08bb385'} as const
const paired = (prefix:string, control:keyof typeof commits, names:string[]) => {
  const selected = rows.filter(r => r.phase === 'timing' && r.label.startsWith(prefix)).sort((a,b)=>Number(a.label.split('-').at(-1))-Number(b.label.split('-').at(-1)))
  if (selected.length !== 6) throw Error(`${prefix}: expected six ordered samples, got ${selected.length}`)
  const pairs = [selected.slice(0,2),selected.slice(2,4),selected.slice(4,6)].map(pair => {
    const candidate = pair.find(r=>r.head.startsWith(commits.r70)), baseline = pair.find(r=>r.head.startsWith(commits[control]))
    if (!candidate || !baseline) throw Error(`${prefix}: missing paired revision`)
    return {candidate,baseline}
  })
  const stats = Object.fromEntries(names.map(name => {
    const c=pairs.map(p=>metric(p.candidate,name)), b=pairs.map(p=>metric(p.baseline,name))
    if (c.some(x=>x===undefined)||b.some(x=>x===undefined)) return [name,null]
    const cv=c as number[], bv=b as number[], logs=cv.map((x,i)=>Math.log(x/bv[i]!)), m=mean(logs), s=sd(logs), t=4.302652729911275
    return [name,{candidate:cv,baseline:bv,candidateMedian:median(cv),baselineMedian:median(bv),medianRatio:median(cv)/median(bv),pairedGeometricMeanRatio:Math.exp(m),paired95LogT:[Math.exp(m-t*s/Math.sqrt(3)),Math.exp(m+t*s/Math.sqrt(3))],candidateMean:mean(cv),candidateSampleSd:sd(cv),baselineMean:mean(bv),baselineSampleSd:sd(bv)}]
  }))
  return {control, pairs:pairs.map(p=>({candidate:{label:p.candidate.label,head:p.candidate.head},baseline:{label:p.baseline.label,head:p.baseline.head}})), stats}
}
const result = {
 schema:'gdp-0502-slowdown-summary/v1',
 observationCount:rows.length,
 assertionsAllPassed:rows.filter(r=>r.phase==='timing').every(r=>r.whole?.status===0),
 primary: [paired('policy-c149','c149',['lawMs','checkWallMs','loweringRenamingResidualMs','ioWriteMs','testMs','processWallMs']),paired('policy-c96','c96',['lawMs','checkWallMs','loweringRenamingResidualMs','ioWriteMs','testMs','processWallMs'])],
 unsoundHistoricalDiagnosticOnly: paired('policy-c08','c08',['lawMs','checkWallMs','loweringRenamingResidualMs','ioWriteMs','testMs','processWallMs']),
 largerCase: paired('exists-c149','c149',['testMs','processWallMs']),
 binderCounts: rows.filter(r=>r.phase==='counts').map(r=>({label:r.label,head:r.head,binder:r.direct?.binder,lawMs:r.direct?.lawMs,checkWallMs:r.direct?.checkWallMs}))
}
writeFileSync(output, JSON.stringify(result,null,2)+'\n')
console.log(JSON.stringify({observationCount:result.observationCount,assertionsAllPassed:result.assertionsAllPassed}))
