// A CPU profile's top functions by self time and by total time (bun --cpu-prof's .cpuprofile), for a job's log.
//   bun research/protocols/relations/profsum.ts <dir> [n]
import {readdirSync, readFileSync} from 'node:fs'
const dir = process.argv[2]!, top = Number(process.argv[3] ?? 40)
const f = readdirSync(dir).find(x => x.endsWith('.cpuprofile'))!
const p = JSON.parse(readFileSync(`${dir}/${f}`, 'utf8'))
const nodes = new Map<number, any>(p.nodes.map((n: any) => [n.id, n])), parent = new Map<number, number>()
for (const n of p.nodes) for (const c of n.children ?? []) parent.set(c, n.id)
const self = new Map<string, number>(), total = new Map<string, number>()
const key = (n: any) => `${n.callFrame.functionName || '(anon)'} ${n.callFrame.url.split('/').pop()}:${n.callFrame.lineNumber + 1}`
p.samples.forEach((s: number, i: number) => {
  const d = p.timeDeltas[i] ?? 0, n = nodes.get(s)
  self.set(key(n), (self.get(key(n)) ?? 0) + d)
  const seen = new Set<string>()
  for (let id: number | undefined = s; id !== undefined; id = parent.get(id)) { const k = key(nodes.get(id)); if (!seen.has(k)) { seen.add(k); total.set(k, (total.get(k) ?? 0) + d) } }
})
const show = (m: Map<string, number>) => [...m].sort((a, b) => b[1] - a[1]).slice(0, top).map(([k, v]) => `${Math.round(v / 1000)} ms ${k}`).join('\n')
console.log(`== self\n${show(self)}\n== total\n${show(total)}`)
