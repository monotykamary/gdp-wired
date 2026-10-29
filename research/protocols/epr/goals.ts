import {writeFileSync} from 'node:fs'
import {lawInstances} from '../../../kernel/prove.ts'
import {obligations} from '../../../kernel/kernel.ts'
import {protocols} from '../../../research/protocols/models.ts'
const [id, dir] = process.argv.slice(2), p = protocols.find(q => q.id === id)!, r = p.make()
const laws = [...r.kindLaws(), ...p.human(r), ...p.laws(r)], m = r.machine
// Each map's key pattern, as the rule reads it: of its reads in the step, the flags and the laws (not the kinds' laws),
// the one with the most parts (the coefficients of a key Σ c·x of distinct names: Table 4096,64,1; Leader 1).
const sig = (e: any): number[] | undefined => { const acc: [string, number][] = []; const go = (x: any, k: number): boolean => x.op === 'var' ? (acc.push([x.name, k]), true) : x.op === 'mul' ? go(x.a, k * x.k) : x.op === 'add' ? go(x.a, k) && go(x.b, k) : false; return go(e, 1) && new Set(acc.map(a => a[0])).size === acc.length ? acc.map(a => a[1]).sort((a, b) => b - a) : undefined }
const patterns: Record<string, number[]> = {}
const each = new Set(Object.values(m.step.maps ?? {}).flatMap((w: any) => ('each' in w ? [w.each] : [])))
const scan = (o: any) => { if (o && typeof o === 'object') { if (o.op === 'get' && !(o.key.op === 'var' && each.has(o.key.name))) { const s2 = sig(o.key); if (s2 && s2.length > (patterns[o.map]?.length ?? 0)) patterns[o.map] = s2 } Object.values(o).forEach(scan) } }
scan(m.step); scan(m.assume); for (const l of laws) if (!(l.name.startsWith('every ') && l.name.endsWith('of its kind'))) scan(l.holds)
laws.forEach((l, i) => {
  if (l.name.startsWith('every ') && l.name.endsWith('of its kind')) return
  const g = obligations(m, laws, {[l.name]: lawInstances(m, laws, i)}, i).find(x => x.name.endsWith('@step'))!
  const f = `${dir}/${id}-${i}.json`; writeFileSync(f, JSON.stringify({...g, patterns})); console.log(f, g.name, g.hyps.length)
})
