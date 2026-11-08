// Read-only Track M source/input snapshot. Never edit or execute a job in that worktree.
import {execFileSync} from 'node:child_process'
import {copyFileSync, existsSync, mkdirSync, readFileSync, statSync, writeFileSync} from 'node:fs'
import {dirname, join} from 'node:path'
import {createHash} from 'node:crypto'
const [source, out] = process.argv.slice(2) as [string, string]
const paths = ['core', 'kernel', 'native', 'research/track-m', 'research/protocols', 'package.json', 'bun.lock']
const files = execFileSync('git', ['-C', source, 'ls-files', '-z', '--cached', '--others', '--exclude-standard', '--', ...paths]).toString().split('\0').filter(Boolean)
const manifest: Record<string, string> = {}
const copy = (from: string, to: string, id: string) => {
  mkdirSync(dirname(to), {recursive: true}); copyFileSync(from, to)
  manifest[id] = createHash('sha256').update(readFileSync(from)).digest('hex')
}
for (const file of new Set(files)) if (existsSync(join(source, file)) && statSync(join(source, file)).isFile()) copy(join(source, file), join(out, 'snapshot', file), file)
for (const file of ['quorum.json', 'input.json']) copy(join(source, 'runs/track-m/canonical-capture-v1/fixtures', file), join(out, 'replay-input', file), 'replay-input/' + file)
// Its legacy checker is byte-identical to main 8610af26; use the proved extension for both sides of this replay.
copy('kernel/kernel.ts', join(out, 'snapshot/kernel/kernel.ts'), 'snapshot-checker')
writeFileSync(join(out, 'manifest.json'), JSON.stringify({source, head: execFileSync('git', ['-C', source, 'rev-parse', 'HEAD']).toString().trim(), files: manifest}, null, 2) + '\n')
console.log(JSON.stringify({files: Object.keys(manifest).length, out}))
