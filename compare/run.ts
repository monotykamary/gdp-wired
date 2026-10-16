// The comparison's measurements, for each tool (gdp-wired, Bend 2, plain Lean 4) and rule (budget, caps, window):
// lines of rule code, of law statements and of proof (non-blank, non-comment lines between `--- rule`, `--- laws`,
// `--- proofs` markers; Bend's `--- evidence` is rule code too, the comparison evidence its proofs case on), the wall
// time to check (median of RUNS runs), whether it checked, a broken variant per rule that each tool must reject, and
// what each one emits to run. Runs where bun, Lean 4.34.0 and the Bend repo are (compare/modal_compare.py on Modal):
//
//   BEND=/path/to/bend bun compare/run.ts
import {mkdirSync, mkdtempSync, readFileSync, statSync, writeFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'

const GDP = resolve(import.meta.dir, '..')
const BEND = process.env.BEND ?? resolve(GDP, '..', 'bend')
const RUNS = Number(process.env.RUNS ?? 5)
const tmp = mkdtempSync(join(tmpdir(), 'compare-'))
const rules = ['budget', 'caps', 'window'] as const
type Rule = typeof rules[number]
type Tool = 'gdp-wired' | 'bend' | 'bend --verdict' | 'lean'

const file = (tool: 'gdp-wired' | 'bend' | 'lean', r: Rule) =>
  tool === 'gdp-wired' ? join(GDP, 'compare/gdpwired', `${r}.ts`) : tool === 'bend' ? join(GDP, 'compare/bend', `${r}.bend`) : join(GDP, 'compare/lean', `${r[0]!.toUpperCase()}${r.slice(1)}.lean`)

// Lines per section: a marker line `<comment> --- <name>` opens a section; blank lines and whole-line comments don't count.
function lines(path: string, comment: string): Record<string, number> {
  const out: Record<string, number> = {}
  let section = 'header'
  for (const raw of readFileSync(path, 'utf8').split('\n')) {
    const l = raw.trim()
    const m = l.match(new RegExp(`^${comment.replace(/[/]/g, '\\/')} --- (\\w+)`))
    if (m) { section = m[1]!; continue }
    if (l === '' || l.startsWith(comment)) continue
    out[section] = (out[section] ?? 0) + 1
  }
  return out
}

function sh(cmd: string[], cwd = GDP): {code: number, out: string, ms: number} {
  const t0 = performance.now()
  const p = Bun.spawnSync(cmd, {cwd, stdout: 'pipe', stderr: 'pipe', env: {...process.env, BEND_NO_TELEMETRY: '1'}})
  return {code: p.exitCode ?? -1, out: p.stdout.toString() + p.stderr.toString(), ms: performance.now() - t0}
}
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)]!

const check = (tool: Tool, path: string): string[] =>
  tool === 'gdp-wired' ? ['bun', path]
    : tool === 'bend' ? ['bun', join(BEND, 'bend2/main.ts'), path, '--check-only']
    : tool === 'bend --verdict' ? ['bun', join(BEND, 'bend2/main.ts'), path, '--verdict']
    : ['lean', path]
const passed = (tool: Tool, r: {code: number, out: string}) =>
  r.code === 0 && (tool === 'gdp-wired' ? /proven=true checked=true/.test(r.out) : tool === 'lean' ? !/error/.test(r.out) : /ALL PROOFS CHECK/.test(r.out))

// A broken variant per rule, the same bug in every tool: the budget forgets the max cost cap; the day cap is off by
// one (count <= d instead of < d); the window admits at seen <= c instead of seen + 1 <= c. Each must be rejected.
const mutations: Record<'gdp-wired' | 'bend' | 'lean', Record<Rule, [string, string][]>> = {
  'gdp-wired': {
    budget: [['s.plus(min(c, m))', 's.plus(c)']],
    caps: [['Day.at(day).lt(d)', 'Day.at(day).atMost(d)']],
    window: [['seen.plus(1).atMost(c)', 'seen.atMost(c)']],
  },
  bend: {
    budget: [['Nat.add(s, Nat.min(c, m))\n', 'Nat.add(s, c)\n']],
    caps: [['step.day(acct, day, g, d, dec(d, count_day(g, day)))', 'step.day(acct, day, g, 1n+d, dec(1n+d, count_day(g, day)))']],
    window: [['v: Cmp2<1n+seen(l, t, w), c>) -> List<&2, Ent>:', 'v: Cmp2<seen(l, t, w), c>) -> List<&2, Ent>:'], ['step.adm(t, l, w, c, dec(1n+seen(l, t, w), c))', 'step.adm(t, l, w, c, dec(seen(l, t, w), c))']],
  },
  lean: {
    budget: [['then s + min c m else', 'then s + c else']],
    caps: [['cntDay r.day g < d then', 'cntDay r.day g ≤ d then']],
    window: [['seen w r.t l + 1 ≤ c then', 'seen w r.t l ≤ c then']],
  },
}
function mutate(tool: 'gdp-wired' | 'bend' | 'lean', r: Rule): string {
  const src = file(tool, r)
  let text = readFileSync(src, 'utf8')
  for (const [a, b] of mutations[tool][r]) {
    if (!text.includes(a)) throw new Error(`${tool} ${r}: mutation target missing: ${a}`)
    text = text.replace(a, b)
  }
  // The TypeScript variant stays beside the original, for its relative imports; the others go to a temp dir.
  const out = tool === 'gdp-wired' ? join(GDP, 'compare/gdpwired', `.broken-${r}.ts`) : join(tmp, `broken-${r}${tool === 'bend' ? '.bend' : '.lean'}`)
  writeFileSync(out, text)
  return out
}

type Row = {tool: Tool, rule: Rule, rule_lines: number, evidence_lines: number, law_lines: number, proof_lines: number, checked: boolean, median_ms: number, runs_ms: number[], broken_rejected: boolean, note: string}
const rows: Row[] = []

// --verdict builds BendTT's kernel once (cached under ~/.bend/bendtt); time that apart, before any timed run.
const warm = sh(['bun', join(BEND, 'bend2/main.ts'), file('bend', 'budget'), '--verdict'])
console.log(`bend --verdict first run (builds the BendTT kernel with Lean): ${(warm.ms / 1000).toFixed(1)} s, exit ${warm.code}`)
// The floor each tool pays before any rule: bun loading the builders, Bend checking a file that only imports Base, Lean
// on an empty file.
writeFileSync(join(tmp, 'empty.bend'), 'import Base\n')
writeFileSync(join(tmp, 'empty.lean'), '')
const floors: Record<string, number> = {
  'gdp-wired': median(Array.from({length: RUNS}, () => sh(['bun', '-e', `await import(${JSON.stringify(join(GDP, 'core/dsl.ts'))})`]).ms)),
  bend: median(Array.from({length: RUNS}, () => sh(check('bend', join(tmp, 'empty.bend'))).ms)),
  'bend --verdict': median(Array.from({length: RUNS}, () => sh(check('bend --verdict', join(tmp, 'empty.bend'))).ms)),
  lean: median(Array.from({length: RUNS}, () => sh(check('lean', join(tmp, 'empty.lean'))).ms)),
}
console.log(`startup floors, median ms: ${JSON.stringify(Object.fromEntries(Object.entries(floors).map(([k, v]) => [k, Math.round(v)])))}`)
for (const tool of ['gdp-wired', 'bend', 'bend --verdict', 'lean'] as Tool[]) {
  const base = tool === 'bend --verdict' ? 'bend' : tool
  for (const r of rules) {
    const path = file(base, r)
    const ls = lines(path, base === 'gdp-wired' ? '//' : base === 'bend' ? '#' : '--')
    const runs = Array.from({length: RUNS}, () => sh(check(tool, path)))
    const ok = runs.every(x => passed(tool, x))
    const broken = mutate(base, r)
    const b = sh(check(tool, broken))
    if (base === 'gdp-wired') rmSync(broken)
    const note = base === 'gdp-wired' ? (runs[0]!.out.match(/prove_ms=\S+ js_bytes=\S+/)?.[0] ?? '') : ''
    rows.push({tool, rule: r, rule_lines: (ls.rule ?? 0) + (ls.evidence ?? 0), evidence_lines: ls.evidence ?? 0, law_lines: ls.laws ?? 0, proof_lines: ls.proofs ?? 0,
      checked: ok, median_ms: Math.round(median(runs.map(x => x.ms))), runs_ms: runs.map(x => Math.round(x.ms)), broken_rejected: !passed(tool, b), note})
    console.log(`\n### ${tool} ${r}: checked=${ok} median=${Math.round(median(runs.map(x => x.ms)))} ms broken_rejected=${!passed(tool, b)}\n${runs[0]!.out.trim()}\n--- broken variant (exit ${b.code}):\n${b.out.trim().split('\n').slice(0, 8).join('\n')}`)
  }
}

// What each tool gives to run: Bend's -o JS (a program running main) and -o .mjs (its non-IO defs as an ES module),
// gdp-wired's compileJs (printed by each rule file above as js_bytes), Lean's -c C file.
console.log('\n## runtime artifacts')
mkdirSync(join(tmp, 'out'), {recursive: true})
for (const r of rules) {
  const js = join(tmp, 'out', `${r}.js`), mjs = join(tmp, 'out', `${r}.mjs`), c = join(tmp, 'out', `${r}.c`)
  const ej = sh(['bun', join(BEND, 'bend2/main.ts'), file('bend', r), '-o', js])
  const em = sh(['bun', join(BEND, 'bend2/main.ts'), file('bend', r), '-o', mjs])
  const run = ej.code === 0 ? sh(['bun', js]) : {code: -1, out: ej.out, ms: 0}
  const lc = sh(['lean', '-c', c, file('lean', r)])
  const size = (p: string) => { try { return statSync(p).size } catch { return -1 } }
  console.log(`${r}: bend -o .js ${size(js)} bytes (exit ${ej.code}), runs to: ${run.out.trim().split('\n').at(-1)}; bend -o .mjs ${size(mjs)} bytes (exit ${em.code}); lean -c ${size(c)} bytes (exit ${lc.code})`)
}

console.log('\n## table')
console.log('| tool | rule | rule lines (of which evidence) | law lines | proof lines | check, median ms | checked | broken variant rejected |')
console.log('| --- | --- | --- | --- | --- | --- | --- | --- |')
for (const x of rows) console.log(`| ${x.tool} | ${x.rule} | ${x.rule_lines}${x.evidence_lines ? ` (${x.evidence_lines})` : ''} | ${x.law_lines} | ${x.proof_lines} | ${x.median_ms} | ${x.checked ? 'yes' : 'NO'} | ${x.broken_rejected ? 'yes' : 'NO'} |`)
console.log(`\nstartup floors (median ms, no rule): ${Object.entries(floors).map(([k, v]) => `${k} ${Math.round(v)}`).join(', ')}`)
console.log(`RUNS=${RUNS}, ${navigator.hardwareConcurrency} CPUs, bun ${Bun.version}`)
console.log('\n## json\n' + JSON.stringify(rows))
rmSync(tmp, {recursive: true, force: true})
process.exit(rows.every(x => x.checked && x.broken_rejected) ? 0 : 1)
