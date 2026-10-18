// Runs the rules: for one rule, build the Bend and Lean benches to native code, then time each tool's whole command
// at each N (median of RUNS runs) and check that the three print the same checksum. N = 0 is each tool's startup
// floor. A command that runs past LIMIT seconds is stopped, and that tool is not run at larger N. Runs where bun,
// clang 14+, Lean 4.34.0 and the Bend repo are (compare/modal_compare.py with compare/bench/jobs.json on Modal):
//
//   BEND=/path/to/bend bun compare/bench/run.ts budget|caps|window
//
// The benches: compare/bench/gdpwired.ts imports each rule from compare/gdpwired/ and runs `.compiled()`;
// compare/bench/bend/<rule>.bend and compare/bench/lean/<Rule>.lean are the compare files, unchanged up to the `--- run`
// marker (checked here), with a main that takes N in place of the demo run.
import {mkdtempSync, readFileSync, statSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'

const GDP = resolve(import.meta.dir, '../..')
const BEND = process.env.BEND ?? resolve(GDP, '..', 'bend')
const RUNS = Number(process.env.RUNS ?? 3)
const LIMIT = Number(process.env.LIMIT ?? 300)
const NS = (process.env.NS ?? '0,1000,10000,100000').split(',').map(Number)
const rule = process.argv[2] as 'budget' | 'caps' | 'window'
if (!['budget', 'caps', 'window'].includes(rule)) { console.error('usage: bun compare/bench/run.ts budget|caps|window'); process.exit(2) }
const Rule = rule[0]!.toUpperCase() + rule.slice(1)
const tmp = mkdtempSync(join(tmpdir(), `bench-${rule}-`))

function sh(cmd: string[], timeout = LIMIT * 1000): {code: number, out: string, err: string, ms: number, killed: boolean} {
  const t0 = performance.now()
  const p = Bun.spawnSync(cmd, {cwd: GDP, stdout: 'pipe', stderr: 'pipe', timeout, env: {...process.env, BEND_NO_TELEMETRY: '1'}})
  const ms = performance.now() - t0
  return {code: p.exitCode ?? -1, out: p.stdout.toString(), err: p.stderr.toString(), ms, killed: p.exitCode === null || ms >= timeout}
}
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)]!
const fail = (msg: string): never => { console.log(`FAIL ${msg}`); process.exit(1) }

// The rule code each tool runs is the code it proved: the bench files equal the compare files up to `--- run`.
for (const [orig, bench, marker] of [[`compare/bend/${rule}.bend`, `compare/bench/bend/${rule}.bend`, '# --- run'], [`compare/lean/${Rule}.lean`, `compare/bench/lean/${Rule}.lean`, '-- --- run']] as const) {
  const head = (p: string) => { const t = readFileSync(join(GDP, p), 'utf8'), i = t.indexOf(`\n${marker}\n`); if (i < 0) fail(`${p}: no ${marker}`); return t.slice(0, i) }
  if (head(orig) !== head(bench)) fail(`${bench} differs from ${orig} before ${marker}`)
  console.log(`${bench}: identical to ${orig} up to ${marker}`)
}

// Builds. Bend: `bend -o <bin>` (the C runtime, built with clang); if that fails, Bend runs through `bun bend2/main.ts`.
const bendBin = join(tmp, rule)
let b = sh(['bun', join(BEND, 'bend2/main.ts'), `compare/bench/bend/${rule}.bend`, '-o', bendBin], 900_000)
const bendNative = b.code === 0
console.log(`build bend -o ${rule}: exit ${b.code}, ${(b.ms / 1000).toFixed(2)} s${bendNative ? `, ${statSync(bendBin).size} bytes` : `\n${b.out}${b.err}`}`)
const leanC = join(tmp, `${Rule}.c`), leanBin = join(tmp, `lean_${rule}`)
b = sh(['lean', '-c', leanC, `compare/bench/lean/${Rule}.lean`], 900_000)
console.log(`build lean -c ${Rule}.c (checks the theorems too): exit ${b.code}, ${(b.ms / 1000).toFixed(2)} s`)
if (b.code !== 0) fail(`lean -c\n${b.out}${b.err}`)
const prefix = sh(['lean', '--print-prefix']).out.trim()
b = sh([join(prefix, 'bin/leanc'), '-O3', leanC, '-o', leanBin], 900_000)
console.log(`build leanc -O3: exit ${b.code}, ${(b.ms / 1000).toFixed(2)} s${b.code === 0 ? `, ${statSync(leanBin).size} bytes` : ''}`)
if (b.code !== 0) fail(`leanc\n${b.out}${b.err}`)

const tools: [string, (n: number) => string[]][] = [
  ['gdp-wired', n => ['bun', 'compare/bench/gdpwired.ts', rule, String(n)]],
  [bendNative ? 'bend' : 'bend (bun bend2/main.ts)', n => bendNative ? [bendBin, String(n)] : ['bun', join(BEND, 'bend2/main.ts'), `compare/bench/bend/${rule}.bend`, String(n)]],
  ['lean', n => [leanBin, String(n)]],
]
console.log(`\ncommands: ${tools.map(([name, cmd]) => `${name}: ${cmd(1000).join(' ').replace(tmp + '/', '')}`).join('; ')}`)
console.log(`median of ${RUNS} runs of the whole command, a run stopped after ${LIMIT} s\n`)
console.log(['rule', 'N', ...tools.map(([t]) => `${t} ms`), 'checksum', 'agree'].join('\t'))
const stopped = new Set<string>()
let bad = 0
for (const n of NS) {
  const cells: string[] = [], sums: string[] = []
  for (const [name, cmd] of tools) {
    if (stopped.has(name)) { cells.push('not run'); continue }
    const ms: number[] = []
    let out = ''
    for (let i = 0; i < RUNS; i++) {
      const r = sh(cmd(n))
      if (r.killed) { stopped.add(name); break }
      if (r.code !== 0) fail(`${name} N=${n}: exit ${r.code}\n${r.out}${r.err}`)
      ms.push(r.ms); out = r.out.trim()
    }
    if (stopped.has(name)) { cells.push(`> ${LIMIT} s`); continue }
    cells.push(median(ms).toFixed(0)); sums.push(out)
  }
  const agree = sums.every(s => s === sums[0])
  if (!agree) bad++
  console.log([rule, n, ...cells, sums[0] ?? '', agree ? (sums.length === tools.length ? 'yes' : `yes (${sums.length} of ${tools.length})`) : `NO: ${sums.join(' | ')}`].join('\t'))
}
process.exit(bad ? 1 : 0)
