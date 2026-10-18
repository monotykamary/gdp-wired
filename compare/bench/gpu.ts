// Bend's GPU path on the same three rules: each Bend bench with its run handed to the GPU (`run!(...)` in place of
// `run(...)` in the bench's own entry point, the rule and its proofs unchanged), built with CUDA, timed beside the plain
// CPU binary of compare/bench/run.ts and the GPU binary with its GPU off (`--gpu off`: the ! call on the CPU lanes). A
// rule's run is a fold over the requests, each step needing the state the one before left, so there is no parallel
// work to hand out: this measures what the GPU path costs such a program, nothing it could speed up. Runs where bun,
// clang 19+, CUDA 12 or 13 at $CUDA_HOME and the Bend repo are (compare/bench/modal_gpu.py on Modal):
//
//   BEND=/path/to/bend bun compare/bench/gpu.ts
import {existsSync, mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'

const GDP = resolve(import.meta.dir, '../..')
const BEND = process.env.BEND ?? resolve(GDP, '..', 'bend')
const RUNS = Number(process.env.RUNS ?? 3)
const LIMIT = Number(process.env.LIMIT ?? 300)
const NS = (process.env.NS ?? '0,1000,10000').split(',').map(Number)
const tmp = mkdtempSync(join(tmpdir(), 'bench-gpu-'))
// The checksums the CPU runs printed (compare/README.md, "Running the rules").
const WANT: Record<string, Record<number, string>> = {
  budget: {0: '0', 1000: '6558', 10000: '65625', 100000: '656250'},
  caps: {0: '0 0 0', 1000: '452 231196 81141', 10000: '748 374281 133771', 100000: '750 375000 134095'},
  window: {0: '0 0 0', 1000: '120 98 56848', 10000: '1189 1028 5944251'},
}

function sh(cmd: string[], timeout = LIMIT * 1000) {
  const t0 = performance.now()
  const p = Bun.spawnSync(cmd, {cwd: tmp, stdout: 'pipe', stderr: 'pipe', timeout, env: {...process.env, BEND_NO_TELEMETRY: '1'}})
  const ms = performance.now() - t0
  return {code: p.exitCode ?? -1, out: p.stdout.toString().trim(), err: p.stderr.toString(), ms, killed: p.exitCode === null || ms >= timeout}
}
const median = (xs: number[]) => [...xs].sort((a, b) => a - b)[Math.floor(xs.length / 2)]!
const fail = (msg: string): never => { console.log(`FAIL ${msg}`); process.exit(1) }

console.log(sh(['nvidia-smi', '--query-gpu=name,driver_version,memory.total', '--format=csv,noheader']).out)
// PROBE=1: the guide's own parallel example (pow2!), to tell the GPU path from the rules.
if (process.env.PROBE) {
  writeFileSync(join(tmp, 'pow2.bend'), `import Base\n\ndef pow2(+n: Nat) -> U32:\n  match n:\n    case 0n:\n      1\n    case 1n+p:\n      a b = pow2(p) pow2(p)\n      (a + b : U32)\n\ndef main() -> IO(Unit):\n  IO.print(U32.show(pow2!(20n)))\n`)
  const b = sh(['bun', join(BEND, 'bend2/main.ts'), 'pow2.bend', '-o', 'pow2'], 900_000)
  console.log(`pow2 build exit ${b.code}${existsSync(join(tmp, 'pow2.gpu')) ? ', GPU program built' : ''}\n${b.err.slice(-2000)}`)
  for (const cmd of [['./pow2'], ['./pow2', '--gpu', 'off']]) {
    const p = sh(cmd, 60_000)
    console.log(`${cmd.join(' ')}: exit ${p.code} ${p.killed ? 'STOPPED at 60 s' : ''} ${Math.round(p.ms)} ms out=${p.out} err=${p.err.slice(-1500)}`)
  }
  process.exit(0)
}
const rows: string[] = ['| rule | N | CPU binary ms | GPU binary, GPU on ms | GPU binary, --gpu off ms | checksum |', '| --- | --- | --- | --- | --- | --- |']
for (const rule of ['budget', 'caps', 'window'] as const) {
  const src = readFileSync(join(GDP, `compare/bench/bend/${rule}.bend`), 'utf8')
  const at = src.indexOf('\ndef bench('), end = src.indexOf('\ndef ', at + 1)
  const body = src.slice(at, end)
  if ((body.match(/\brun\(/g) ?? []).length !== 1) fail(`${rule}: the bench calls run once`)
  const gpuSrc = src.slice(0, at) + body.replace(/\brun\(/, 'run!(') + src.slice(end)
  writeFileSync(join(tmp, `${rule}.bend`), src)
  writeFileSync(join(tmp, `${rule}_gpu.bend`), gpuSrc)
  for (const [file, bin] of [[`${rule}.bend`, rule], [`${rule}_gpu.bend`, `${rule}_gpu`]] as const) {
    const b = sh(['bun', join(BEND, 'bend2/main.ts'), file, '-o', bin], 900_000)
    if (b.code !== 0) fail(`${file}: build failed\n${b.out}\n${b.err}`)
    console.log(`built ${bin} in ${Math.round(b.ms)} ms${existsSync(join(tmp, `${bin}.gpu`)) ? `, with its GPU program ${bin}.gpu` : ''}`)
  }
  if (!existsSync(join(tmp, `${rule}_gpu.gpu`))) fail(`${rule}_gpu: no GPU program was built (is CUDA at $CUDA_HOME?)`)
  const modes: [string, string[]][] = [['cpu', [`./${rule}`]], ['gpu', [`./${rule}_gpu`]], ['gpuoff', [`./${rule}_gpu`, '--gpu', 'off']]]
  const stopped = new Set<string>()
  for (const n of NS) {
    const cells: string[] = []
    let sum = ''
    for (const [mode, cmd] of modes) {
      if (stopped.has(mode)) { cells.push('—'); continue }
      const times: number[] = []
      let cell = ''
      for (let r = 0; r < RUNS; r++) {
        const p = sh([...cmd, String(n)])
        if (p.killed) { stopped.add(mode); cell = `stopped at ${LIMIT} s`; break }
        if (p.code !== 0) fail(`${rule} ${mode} N=${n}: exit ${p.code}\n${p.err}`)
        if (WANT[rule]![n] !== undefined && p.out !== WANT[rule]![n]) fail(`${rule} ${mode} N=${n}: printed ${p.out}, the CPU runs printed ${WANT[rule]![n]}`)
        sum = p.out
        times.push(p.ms)
      }
      cells.push(cell || String(Math.round(median(times))))
      console.log(`${rule} N=${n} ${mode}: ${cells.at(-1)}`)
    }
    rows.push(`| ${rule} | ${n.toLocaleString('en-US')} | ${cells.join(' | ')} | ${sum} |`)
  }
}
console.log(rows.join('\n'))
