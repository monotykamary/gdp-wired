// Research-only preload: bounded transport of production SAT witnesses and root
// queries. Use beside research/query/dump.ts with DUMP_ALL=1 for the full local
// capture; stdout contains only selected helper queries, compressed for boat.
import {gzipSync} from 'node:zlib'
import {countsDump} from '../../core/counts.ts'
import {finiteDump} from '../../core/finite-houdini.ts'
import {queryHook} from '../../kernel/prove.ts'
const enabled = process.env.T14_CAPTURE === '1'
if (enabled) {
  let family: unknown, beforeFinite: unknown
  const finiteDrops: unknown[] = []
  finiteDump.onStart = value => { beforeFinite = {...value, machine: {...value.machine, counts: {...value.machine.counts}}} }
  finiteDump.onDrop = drop => { finiteDrops.push({...drop, pre: {...drop.pre, maps: Object.fromEntries(Object.entries(drop.pre.maps).map(([k, v]) => [k, [...v]]))}, post: {...drop.post, maps: Object.fromEntries(Object.entries(drop.post.maps).map(([k, v]) => [k, [...v]]))}, request: Object.fromEntries(Object.entries(drop.request).map(([k, v]) => [k, v instanceof Map ? [...v] : v]))}) }
  const witnesses: unknown[] = [], roots: unknown[] = [], seen = new Set<string>()
  const old = countsDump.on
  countsDump.on = value => {
    old?.(value)
    const v = value as Record<string, unknown>
    if (v.phase === 'candidates') family = value
    if (v.stuck === 'sat' && v.witness && witnesses.length < 40) witnesses.push(value)
  }
  const previous = queryHook.on
  queryHook.on = q => {
    previous?.(q)
    const outcome = 'tree' in q.out ? 'tree' : q.out.stuck
    const wanted = /stored guard.*disabled\/0|canVote\/3|CV\[a\]=CV\[b\].*CfgT\[a\]=CfgT\[b\]|one primary per term/.test(q.goal.name)
    const key = `${q.kind}:${q.goal.name}:${outcome}`
    if (wanted && outcome !== 'tree' && !seen.has(key) && roots.length < 16) { seen.add(key); roots.push({kind: q.kind, goal: q.goal, work: q.work, ms: q.ms, outcome, out: q.out}) }
  }
  process.on('exit', () => {
    const zip = gzipSync(JSON.stringify({family, beforeFinite, finiteDrops, witnesses, roots}))
    console.log(`T14_CAPTURE_BYTES ${zip.length}`)
    if (zip.length > 210_000) { console.log('T14_CAPTURE_OVERFLOW'); return }
    console.log(`T14_CAPTURE_GZIP_BASE64 ${zip.toString('base64')}`)
  })
}
