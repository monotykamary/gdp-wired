// A batch's logs (modal/run.py --jobs research/extract/jobs.json --out <dir>) into research/extract/results/: each job's
// results file as it printed it, and the rules extracted from the examples.
//
//   bun research/extract/collect.ts <dir>
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

const dir = process.argv[2]
if (!dir) throw new Error('usage: bun research/extract/collect.ts <batch dir>')
const out = join(import.meta.dir, 'results')
mkdirSync(join(out, 'rules'), {recursive: true})
const sections = (log: string) => {
  const parts: Record<string, string> = {}
  let name: string | undefined, buf: string[] = []
  for (const line of log.split('\n')) {
    const m = /^--- (.+)$/.exec(line)
    if (m) { if (name) parts[name] = `${buf.join('\n').trim()}\n`; name = m[1]!; buf = [] } else if (name) buf.push(line)
  }
  if (name) parts[name] = `${buf.join('\n').trim()}\n`
  return parts
}
const read = (job: string) => sections(readFileSync(join(dir, `${job}.log`), 'utf8'))
const ours = read('extract-ours'), real = read('extract-realworld'), verdicts = read('extract-verdicts')
writeFileSync(join(out, 'ours.jsonl'), ours['results.jsonl'] ?? '')
writeFileSync(join(out, 'realworld.jsonl'), real['results.jsonl'] ?? '')
writeFileSync(join(out, 'verdicts.jsonl'), verdicts['verdicts.jsonl'] ?? '')
for (const [k, v] of Object.entries(ours)) if (k.startsWith('rule ')) writeFileSync(join(out, 'rules', k.slice(5)), v)
console.log(`results/: ${Object.keys(ours).filter(k => k.startsWith('rule ')).length} rules, ${(ours['results.jsonl'] ?? '').trim().split('\n').length} + ${(real['results.jsonl'] ?? '').trim().split('\n').length} sources, ${(verdicts['verdicts.jsonl'] ?? '').trim().split('\n').length} verdict rows`)
