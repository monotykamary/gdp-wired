// Source check for the final research files without altering an inherited failed probe.
// This is not a general replacement for `bun run check`; the full-worktree failure is reported.
import {readFileSync, writeFileSync, mkdtempSync, existsSync} from 'node:fs'
import {resolve, join} from 'node:path'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const root = process.cwd(), old = 'research/verify-all/paxos-law12-probe-v1.ts'
const excluded = resolve(old), base = JSON.parse(readFileSync('tsconfig.json', 'utf8')), present = existsSync(excluded)
console.log('SOURCE_CHECK_SCOPE', JSON.stringify({base:'tsconfig.json',additionalExclusion:present ? old : null,reason:'inherited failed, uncommitted v1; final proof uses v2',excludedSha256:present ? createHash('sha256').update(readFileSync(excluded)).digest('hex') : null}))
// Keep the temporary config under this checkout so default @types resolution uses its node_modules.
const dir = mkdtempSync(join(root, 'research/verify-all/.paxos-source-check-')), config = join(dir, 'tsconfig.json')
writeFileSync(config, JSON.stringify({extends:join(root, 'tsconfig.json'),exclude:[...base.exclude.map((p:string) => resolve(p)),...(present ? [excluded] : [])]}))
for (const [cmd, args] of [
  ['bunx', ['tsc','-p',config]],
  ['bunx', ['oxlint','--type-aware','--deny-warnings','--disable-nested-config','--ignore-pattern',old]],
] as const) {
  console.log('SOURCE_CHECK_COMMAND', JSON.stringify({cmd,args}))
  const out = spawnSync(cmd, [...args], {stdio:'inherit',timeout:600000})
  if (out.error) throw out.error
  if (out.status !== 0) process.exit(out.status ?? 1)
}
console.log('SOURCE_CHECK_PASS: base tree and final research sources; only inherited uncommitted probe-v1 excluded')
