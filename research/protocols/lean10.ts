// gen/lean10: a protocol's safety law proven with nothing written (run.ts's search), then its final law set (the kinds',
// the caller's and every law the search found, as the verdict returns them) exported through the Lean path the suite
// uses (lean-kernel/emit.ts's toLean: cyclic certificates where the cyclic route covers the machine, the usual trees
// otherwise), for `lean` to check against the twin.
//   bun research/protocols/lean10.ts <id> <ms> <out.lean>
// One JSON line: the search's verdict and time, what was found, the export's route (certReport), bytes and time, or
// the exporter's error.
import {readFileSync, writeFileSync} from 'node:fs'
import {proveRule} from '../../core/dsl.ts'
import {type Law} from '../../core/machine.ts'
import {certReport, toLean} from '../../lean-kernel/emit.ts'
import {protocols} from './models.ts'

const [id = 'lock_server_sync', ms0, file = '/tmp/p.lean'] = process.argv.slice(2), ms = Number(ms0 ?? 60_000)
const p = protocols.find(q => q.id === id)!, r: any = p.make(), laws: Law[] = p.laws(r)
const out: Record<string, unknown> = {id}
// (LEAN10_TRIES: the search again on an unknown, up to that many times; the tries counted)
const t0 = performance.now()
let v: any, tries = 0
// (LEAN10_FROM=<file>: the found laws a run saved (LEAN10_SAVE=1 prints them, one line `SET <json>`), no search)
if (process.env.LEAN10_FROM) v = {proven: true, checked: true, found: {laws: JSON.parse(readFileSync(process.env.LEAN10_FROM, 'utf8')).map((law: Law) => ({law, text: law.name}))}}
else do { v = proveRule(r, laws, {search: {ms}}); tries++ } while (!(v.proven && v.checked) && !v.run && tries < Number(process.env.LEAN10_TRIES ?? 1))
if (process.env.LEAN10_SAVE && v.proven) console.error(`SET ${JSON.stringify((v.found?.laws ?? []).map((f: any) => f.law))}`)
out.tries = tries
out.search = {verdict: v.proven && v.checked ? 'proven' : v.run ? 'refuted' : 'unknown', ms: Math.round(performance.now() - t0), found: v.found?.laws?.length ?? 0,
  some: (v.found?.laws ?? []).filter((f: any) => f.law.some?.length).length, facts: v.found?.facts?.length ?? 0, lemmas: Object.keys(v.found?.lemmas ?? {}).length}
// The export of a law set: its route (certReport) and size, or the exporter's error.
const exportOf = (all: Law[], to: string): Record<string, unknown> => {
  const rule = r.withSumsOf(all), set = [...rule.kindLaws().filter((k: Law) => !all.some(l => l.name === k.name)), ...all]
  const t1 = performance.now()
  try {
    const text = toLean([{id, machine: rule.machine, laws: set}], {title: id})
    writeFileSync(to, text)
    return {ok: true, ms: Math.round(performance.now() - t1), bytes: text.length, laws: set.length, cyclic: certReport.cyclic.length, fast: certReport.fast.length, usual: certReport.usual.map(u => u.why.slice(0, 200)),
      imports: text.split('\n').filter(l => l.startsWith('import ')).map(l => l.slice(7))}
  } catch (e) { return {ok: false, ms: Math.round(performance.now() - t1), error: String((e as Error).stack ?? e).slice(0, 600)} }
}
if (v.proven && v.checked) {
  const found: Law[] = (v.found?.laws ?? []).map((f: any) => f.law)
  // (LEAN10_SOME=written: the written ∃ law added, a stand-in for an ∃ law the verdict's found list leaves out; labelled.
  // LEAN10_SOME=also: the verdict's set first, then, into <out>.standin.lean, the set with the stand-in)
  const extra: Law[] = process.env.LEAN10_SOME ? p.human(r).filter((l: Law) => l.some?.length) : []
  if (process.env.LEAN10_SOME === 'written') { out.standIn = extra.map(l => l.name); out.export = exportOf([...laws, ...found, ...extra], file) }
  else {
    out.export = exportOf([...laws, ...found], file)
    if (process.env.LEAN10_SOME === 'also' && extra.length) out.standIn = {laws: extra.map(l => l.name), export: exportOf([...laws, ...found, ...extra], file.replace(/\.lean$/, '_standin.lean'))}
  }
}
console.log(JSON.stringify(out))
process.exit(0)
