import {proveRule} from '../../core/dsl.ts'
import {smallOf, trueSmall} from '../../core/exists.ts'
import {countsDump} from '../../core/counts.ts'
import {writeFileSync, mkdirSync} from 'node:fs'
import {published} from './published.ts'
const {r, laws} = published(), m = r.machine
const start = performance.now()
console.log(JSON.stringify({samples: smallOf(m).map(s => s.sts.length), laws: laws.map(l => ({name: l.name, holdsOnSamples: trueSmall(m, [l])}))}))
let n = 0
mkdirSync('/tmp/track-m-goals', {recursive: true})
countsDump.on = (g: any) => {
  const name = `${n++}.json`
  writeFileSync(`/tmp/track-m-goals/${name}`, JSON.stringify({kind: 'grow', outcome: g.stuck, goal: {name: g.goal, hyps: g.hyps}}))
  console.log(JSON.stringify({dump: name, law: g.law, goal: g.goal, hyps: g.hyps.length, stuck: g.stuck, witness: g.witness}))
}
const v = proveRule(r, laws, {search: false})
console.log(JSON.stringify({ms: performance.now() - start, verdict: v}))
