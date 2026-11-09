// Research-only, bounded transport. Observation never changes proof policy.
import {gzipSync} from 'node:zlib'
import {countsDump} from '../../core/counts.ts'
import {finiteDump} from '../../core/finite-houdini.ts'
if (process.env.T14_CAPTURE === '1') {
  let family: unknown, beforeFinite: unknown
  const finiteDrops: unknown[] = [], witnesses: unknown[] = [], roots: {law: string, pass: number, kind: string, outcome: string, goal: {name: string, hyps: unknown[]}}[] = []
  const seen = new Set<string>(), witnessKeys = new Set<string>()
  const wanted = (name: string) => /stored guard.*disabled\/0|canVote\/3|CV\[a\]=CV\[b\].*CfgT\[a\]=CfgT\[b\]|one primary per term/.test(name)
  finiteDump.onStart = value => { beforeFinite = {...value, machine: {...value.machine, counts: {...value.machine.counts}}} }
  finiteDump.onDrop = drop => { finiteDrops.push({...drop, pre: {...drop.pre, maps: Object.fromEntries(Object.entries(drop.pre.maps).map(([k, v]) => [k, [...v]]))}, post: {...drop.post, maps: Object.fromEntries(Object.entries(drop.post.maps).map(([k, v]) => [k, [...v]]))}, request: Object.fromEntries(Object.entries(drop.request).map(([k, v]) => [k, v instanceof Map ? [...v] : v]))}) }
  const old = countsDump.on
  countsDump.on = value => {
    old?.(value)
    const v = value as any, law = String(v.law ?? ''), outcome = String(v.stuck ?? v.phase ?? '')
    if (v.phase === 'candidates') family = value
    if (outcome === 'sat' && v.witness) {
      const compact = {law, pass: v.pass, phase: v.phase ?? 'candidate-model', witness: v.witness}
      const key = JSON.stringify(compact)
      if (!witnessKeys.has(key)) { witnessKeys.add(key); witnesses.push(compact) }
    }
    if (!wanted(law) || !['sat', 'unknown'].includes(outcome)) return
    const goal = typeof v.goal === 'object' ? v.goal : Array.isArray(v.hyps) ? {name: `${law} @step`, hyps: v.hyps} : undefined
    if (!goal?.hyps) return
    const key = `${law}:${v.pass}:${outcome}`
    if (!seen.has(key)) { seen.add(key); roots.push({law, pass: v.pass, kind: outcome === 'sat' ? 'decide' : 'grow', outcome, goal}) }
  }
  process.on('exit', () => {
    const kept = [...roots], omittedRoots: unknown[] = []
    const pack = () => gzipSync(JSON.stringify({family, beforeFinite, finiteDrops, witnesses, roots: kept, omittedRoots}))
    let zip = pack()
    while (zip.length > 180_000 && kept.length) { const r = kept.pop()!; omittedRoots.push({law: r.law, pass: r.pass, outcome: r.outcome}); zip = pack() }
    console.log(`T14_CAPTURE_BYTES ${zip.length}`)
    if (zip.length > 180_000) { console.log('T14_CAPTURE_OVERFLOW'); return }
    console.log(`T14_CAPTURE_GZIP_BASE64 ${zip.toString('base64')}`)
  })
}
