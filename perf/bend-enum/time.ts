// Times each Bend binary three ways, the median of five runs, and checks its output against the JS count.
const expected = new Map(require('fs').readFileSync('js.jsonl', 'utf8').trim().split('\n').map((line: string) => JSON.parse(line)).map((r: any) => [r.k, String(r.expected)]))
const run = (args: string[]) => {
  const times: number[] = []
  let out = ''
  for (let i = 0; i < 5; i++) {
    const started = performance.now()
    const result = Bun.spawnSync(args)
    times.push(performance.now() - started)
    out = result.stdout.toString().trim()
  }
  times.sort((a, b) => a - b)
  return {ms: Math.round(times[2]! * 10) / 10, out}
}
for (const k of [24, 28, 30, 31]) {
  const seq = run([`./k${k}-cpu`, '--threads', '1', '--gpu', 'off'])
  const par = run([`./k${k}-cpu`, '--gpu', 'off'])
  const gpu = run([`./k${k}`])
  const ok = [seq, par, gpu].every(r => r.out === expected.get(k))
  console.log(JSON.stringify({k, seqMs: seq.ms, parMs: par.ms, gpuMs: gpu.ms, agree: ok}))
}
