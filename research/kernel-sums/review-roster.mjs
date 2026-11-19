import { registerHooks } from 'node:module'
import { readFileSync } from 'node:fs'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
const url = p => pathToFileURL(resolve(p)).href
const dsl = url('core/dsl.ts')
const hook = registerHooks({ load(uri, context, next) {
  const result = next(uri, context)
  if (uri !== dsl) return result
  let source = Buffer.from(result.source).toString('utf8')
  for (const [find, names] of [
    [/^export function proveRule\(.*\): Verdict \{/m, '[r,laws,[],opts]'],
    [/^export function proveSteps\(.*\): Verdict \{/m, '[r,laws,stepLaws,opts]'],
    [/^export function proveLeadsTo\(.*\): Verdict \{/m, '[r,laws,[],opts,l]'],
    [/^export const proveDecision = .*: Verdict => \{/m, '[d.rule,[],[],opts,d]'],
  ]) {
    if (!find.test(source)) throw new Error(`No entry for ${find}`)
    source = source.replace(find, `$&\n  if (globalThis.__lemmaBankCapture) throw { capture: ${names} };`)
  }
  return { ...result, source }
}})
const { corpus, broken } = await import(url('research/realworld/corpus.ts'))
const { protocols: ic3 } = await import(url('research/protocols/ic3syn/models.ts'))
const { protocols: duo } = await import(url('research/protocols/models.ts'))
const { proveRule, proveSteps } = await import(dsl)
hook.deregister()
if (broken.length) throw new Error(JSON.stringify(broken))
export { corpus, ic3, duo, proveRule, proveSteps }
export function argsFor(law) {
  globalThis.__lemmaBankCapture = true
  try { law.prove(60000); throw new Error(`no capture for ${law.name}`) }
  catch (e) { if (!e?.capture?.[0]) throw e; return e.capture }
  finally { delete globalThis.__lemmaBankCapture }
}

// Recheck only rows for which the aggregate recognizers may propose a proof.
// Liveness and step-law paths do not invoke this new strategy.
const {proposeFilteredCounters}=await import(url('core/filtered-sum-candidates.ts'))
const {weightedCandidates}=await import(url('core/aggregate-weighted/candidates.ts'))
const {writeFileSync}=await import('node:fs')
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR, hit=[]
let i=-1
for(const item of corpus)for(const [k,law] of item.laws.entries()){
  i++
  if(law.form!=='invariant')continue
  const [r,ls]=argsFor(law)
  if(ls.length!==1)continue
  const m=r.machine,l=ls[0],maps=Object.values(m.step.maps??{})
  if(m.history||m.primitiveFailure||Object.keys(m.sums??{}).length||Object.keys(m.counts??{}).length||Object.keys(m.fns??{}).length||m.facts?.length||m.inputMaps?.length||l.keys?.length||l.some?.length||l.ex)continue
  const active=l.forall?maps.some(w=>'each'in w)&&maps.some(w=>!('each'in w))&&weightedCandidates(m,l).length>0:
    maps.length===1&&'each'in maps[0]&&proposeFilteredCounters(m,l).some(p=>p.bound.op==='var')
  if(active)hit.push({i,k,id:item.id,name:law.name})
}
if(i!==466||hit.length<4)throw Error('invalid review roster')
writeFileSync(`${out}/affected.json`,JSON.stringify(hit,null,2)+'\n')
writeFileSync(`${out}/affected.jobs.json`,JSON.stringify(hit.map(({i})=>({name:`review-pair-${i}`,cmd:`bash research/kernel-sums/paired.sh row ${i}`,timeout:190,cpu:1,memory:6144,required_agent_capabilities:{output_files_protocol:1}})),null,2)+'\n')
