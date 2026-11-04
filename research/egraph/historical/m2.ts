// Historical full-context reproduction; no changes to the preserved engine.
import {createHash} from 'node:crypto'
import {readFileSync} from 'node:fs'
import {resolve} from 'node:path'
import {gzipSync} from 'node:zlib'
import type {Machine, Law, E} from '../../../core/machine.ts'
import type {Instances, CountCert, Goal} from '../../../kernel/kernel.ts'
import {EGraph, Meter} from '../match.ts'
const sha = (s: string | Buffer) => createHash('sha256').update(s).digest('hex')
const root = resolve(process.env.ASTRA_BASELINE ?? 'baseline444')
const load = (p: string) => import(`${root}/${p}`)
const {published} = await load('research/protocols/ground-truth/published.ts')
const {proveRule} = await load('core/dsl.ts')
const {withWall} = await load('kernel/prove.ts')
const {countedObligations, checkMC} = await load('kernel/kernel.ts')
type Attempt = {m: Machine, laws: Law[], law: Law, pass: 0 | 1, proof?: {instances: Instances, certs: Record<string, CountCert>}, stuck?: string, failure?: {goal: Goal, witness?: Record<string, number>}}
const counts = await load('core/counts.ts') as {countsAttempt: {on?: (e: Attempt) => void}}
const paths = ['core/counts.ts','core/dsl.ts','kernel/kernel.ts','kernel/prove.ts','research/protocols/ground-truth/published.ts','research/protocols/ground-truth/check.ts','research/protocols/ground-truth/published.test.ts','research/protocols/ic3syn/atomic.ts','research/protocols/ic3syn/models.ts']
const sourceHashes = () => Object.fromEntries(paths.map(p => [p, sha(readFileSync(`${root}/${p}`))]))
const before = sourceHashes()
console.log('SOURCE', JSON.stringify({baseline:'444ece6ebe42d202150bc583c0c55b626b4e32c9', hashes:before, runtime:Bun.version, environment:Object.fromEntries(Object.entries(process.env).filter(([k])=>k.startsWith('GDP_')))}))
const focuses = ['one value decided','P1 proposals unique','P2 vote proposed','P3 decision has quorum','P4 one_b left','P5 choosable']
for (const focus of focuses) {
  const {r, laws} = published('paxos_epr')
  laws.sort((a: Law,b: Law)=>Number(b.name===focus)-Number(a.name===focus))
  const attempts: Attempt[] = [], old = counts.countsAttempt.on
  counts.countsAttempt.on = e => { attempts.push(JSON.parse(JSON.stringify(e)) as Attempt) }
  let verdict
  try { verdict = withWall(performance.now()+25_000,()=>proveRule(r,laws,{search:false})) }
  finally { counts.countsAttempt.on = old }
  const e = attempts.filter(a=>a.law.name===focus).at(-1)
  const proof = e?.proof
  const goals = proof && countedObligations(e.m,e.laws,{[focus]:proof.instances},e.laws.findIndex(l=>l.name===focus)) as {goal:Goal,decls:unknown[]}[] | undefined
  const source = e && JSON.stringify([e.m,e.laws])
  const replay = goals?.map(({goal,decls})=>({name:goal.name,goalSha256:sha(JSON.stringify({goal,decls})),checked:!!proof?.certs[goal.name] && proof.certs[goal.name]!.insts.every(i=>!source!.includes(JSON.stringify(i.wit))) && checkMC(goal.hyps,decls,proof.certs[goal.name])}))
  const checks = [false,true].map(enabled=>{
    const meter = new Meter(100_000,performance.now()+1000), graph = new EGraph(meter)
    if (!e?.failure) return {enabled,status:'not-applicable',reason:'no failed goal captured',instances:0}
    try {
      graph.seed(e.failure.goal.hyps)
      const voteLaw=e.laws.find(l=>l.name==='P2 vote proposed')
      if (!voteLaw?.forall) throw Error('historical P2 law missing')
      const terms:E[]=[]
      const visit=(o:unknown):void=>{if(!o||typeof o!=='object')return; const q=o as Record<string,unknown>;if(q.op==='get'&&q.map==='Vote') terms.push(o as E);for(const v of Object.values(q))if(v&&typeof v==='object')visit(v)}
      visit(voteLaw.holds)
      if (!terms.length) throw Error('historical Vote term not located')
      const matches=enabled?graph.match([terms[0]!],[voteLaw.forall,...voteLaw.keys??[]]):[]
      return {enabled,status:'matched-only',instances:matches.length,matches,reason:'counted certificate bridge not implemented; no proof/flip claimed',matchingUnits:meter.used}
    } catch(error) {return {enabled,status:'unsupported-or-exhausted',reason:String(error),instances:0,matchingUnits:meter.used}}
  })
  const out={focus,verdict,attempts:attempts.length,context:e?.laws.map(l=>l.name),inputSha256:source&&sha(source),failure:e?.failure&&{goal:e.failure.goal.name,sha256:sha(JSON.stringify(e.failure.goal)),hyps:e.failure.goal.hyps.length},baselineChecked:replay?.length===2&&replay.every(x=>x.checked),replay,proofSha256:proof&&sha(JSON.stringify(proof)),comparison:checks}
  console.log('RESULT',JSON.stringify(out))
  if(e){const bytes=JSON.stringify(e);console.log('ARTIFACT',JSON.stringify({name:`m2-${focus.replaceAll(' ','-')}.json`,sha256:sha(bytes),gzipBase64:gzipSync(bytes).toString('base64')}))}
}
const after=sourceHashes();console.log('POSTFLIGHT',JSON.stringify({unchanged:JSON.stringify(before)===JSON.stringify(after),hashes:after}))
if(JSON.stringify(before)!==JSON.stringify(after))throw Error('source changed')
