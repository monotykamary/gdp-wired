// The encoding core/cyclic.ts's machineNodes makes, checked by Lean against Bridge.lean's (cycMOk, part by part) for
// every machine law of the example domains (and each broken variant) the cyclic route covers: what cyc_machine_sound
// needs of an exported proof, besides its trees. Likewise recurNodes' equations (recOk) for the examples' recurrences
// that read no other function, and foldNodes' table (foldOk) for the examples' folds and their broken variants. `bun research/cyclic/bridge.ts <dir> [domain...]` writes one Lean file
// per domain (no proof is grown: the check reads no tree); with --lean it also runs Lean on each (LEAN_PATH set, Bridge
// compiled: modal/suite.json's lean-bridge-sweep) and prints each check that fails.
import {mkdirSync, writeFileSync} from 'node:fs'
import type {Law, Machine} from '../../core/machine.ts'
import {domains} from '../../examples/index.ts'
import {cyclicMachine, foldNodes, hasQuantified, machineNodes, recurNodes} from '../../core/cyclic.ts'
import {cycEncodingLean, cycFoldCheckLean, cycRecurCheckLean} from '../../lean-kernel/emit.ts'
import * as lemmas from '../../examples/lemmas.ts'
import * as functions from '../../examples/functions.ts'
import {orgChart, orgChartLaws, rollup, rollupLaws, signoffLaws, signoffs} from '../../examples/folds.ts'

const out = process.argv[2]
if (!out) throw new Error('usage: bun research/cyclic/bridge.ts <dir> [domain...]')
const lean = process.argv.includes('--lean'), only = process.argv.slice(3).filter(a => a !== '--lean')
mkdirSync(out, {recursive: true})
let machines = 0, laws = 0, outside = 0
for (const d of domains) {
  if (only.length && !only.includes(d.domain)) continue
  const parts: string[] = []
  for (const c of d.cases) {
    if (c.kind !== 'rule') continue
    const variants: [string, typeof c.rule, Law[]][] = [[c.name, c.rule, c.laws], ...c.broken.map((b): [string, typeof c.rule, Law[]] => [`${c.name} (${b.name})`, b.rule, b.laws])]
    for (const [what, rule, ls] of variants) {
      const m = rule.machine
      // (a flag at every key: BridgeRules.lean's cycQMOk, through the sk machine, which this sweep doesn't read)
      if (!cyclicMachine(m, ls) || hasQuantified(m)) { outside++; continue }
      const {facts, specs} = machineNodes(m, ls, {})
      parts.push(`-- ${what}\n${cycEncodingLean(`c${machines}`, facts, specs, {machine: m, laws: ls})}`)
      machines++
      laws += ls.length
    }
  }
  writeFileSync(`${out}/${d.domain.replace(/[^A-Za-z0-9]/g, '_')}.lean`, `import Bridge\nopen Kern\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n${parts.join('\n\n')}\n`)
}
// Recurrences: each FnDef the examples export (a recurrence, or a rule reading one) that reads no other function.
const recurs = new Map<string, NonNullable<NonNullable<Machine['fns']>[string]['recur']> & {name: string}>()
const take = (fns: Machine['fns']) => { for (const [n, f] of Object.entries(fns ?? {})) if (f.recur && !Object.keys(f.recur.uses).length && /^[A-Za-z]\w*$/.test(n)) recurs.set(`${n}:${JSON.stringify(f.recur.next)}`, {...f.recur, name: n}) }
for (const mod of [lemmas, functions] as Record<string, unknown>[]) for (const [key, val] of Object.entries(mod)) {
  if (typeof val !== 'function' || val.length !== 0) continue
  let made: unknown
  try { made = (val as () => unknown)() } catch { continue }
  const o = made as {machine?: Machine, recur?: NonNullable<Machine['fns']>[string]['recur']}
  if (o?.machine) take(o.machine.fns)
  if (o?.recur) take({[key]: o as NonNullable<Machine['fns']>[string]})
}
const rparts = [...recurs.values()].map((r, i) => {
  const {facts} = recurNodes({name: r.name, args: r.args, zero: r.zero, next: r.next, lemmas: r.lemmas, between: r.between, facts: []})
  return cycRecurCheckLean(`r${i}`, facts, {name: r.name, args: r.args, zero: r.zero, next: r.next, lemmas: r.lemmas, between: r.between})
})
// Folds: the examples' and their broken variants.
const folds = [['rollup', rollup(), rollupLaws(rollup())], ['rollup (caps the leaves only)', rollup('caps the leaves only'), rollupLaws(rollup('caps the leaves only'))],
  ['org chart', orgChart(), [...orgChart().lemmas, ...orgChartLaws()]], ['sign-offs', signoffs(), signoffLaws(signoffs())],
  ['sign-offs (ignores the node\'s own sign-off)', signoffs('ignores the node\'s own sign-off'), signoffLaws(signoffs('ignores the node\'s own sign-off'))]] as const
const fparts = folds.map(([what, f, ls], i) => { const {facts, specs} = foldNodes(f.fold, ls as Law[]); return `-- ${what}\n${cycFoldCheckLean(`f${i}`, facts, specs, f.fold, ls as Law[])}` })
writeFileSync(`${out}/recurrences_and_folds.lean`, `import Bridge\nopen Kern\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n${[...rparts, ...fparts].join('\n\n')}\n`)
console.log(`${machines} machines, ${laws} laws; ${outside} outside the cyclic route; ${rparts.length} recurrences; ${folds.length} folds`)
if (lean) {
  const files = [...new Bun.Glob('*.lean').scanSync(out)].sort()
  const runs = await Promise.all(files.map(async f => {
    const p = Bun.spawn(['lean', f], {cwd: out, stdout: 'pipe', stderr: 'pipe'})
    const text = await new Response(p.stdout).text() + await new Response(p.stderr).text()
    return {f, code: await p.exited, text}
  }))
  let checks = 0, failed = 0
  for (const {f, code, text} of runs) {
    const src = (await Bun.file(`${out}/${f}`).text()).split('\n')
    checks += src.filter(l => l.startsWith('-- CHECK')).length
    const bad = [...text.matchAll(/^[^:\n]+\.lean:(\d+):\d+: error/gm)].map(m => Number(m[1]))
    for (const line of bad) { failed++; console.log(`FAIL ${src[line - 2] ?? `line ${line}`}`) }
    if (code !== 0 && !bad.length) { failed++; console.log(`FAIL ${f}: lean exit ${code}\n${text.slice(0, 2000)}`) }
  }
  console.log(`${checks} checks, ${failed} failed`)
  if (failed) process.exit(1)
}
