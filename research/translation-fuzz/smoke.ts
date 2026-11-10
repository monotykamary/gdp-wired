// One reproducible case per family, bounded independently of the full sweep.
import {mkdtempSync, readFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {FAMILIES} from './model.ts'
const dir = mkdtempSync(join(tmpdir(), 'gdp-translation-smoke-'))
try {
  const run = Bun.spawnSync(['timeout', '170', 'bun', join(import.meta.dir, 'run.ts'), '--api', process.cwd(), '--seed', '31', '--count', String(FAMILIES.length), '--case-ms', '10000', '--expect-clean', '--out', join(dir, 'smoke')], {stdout: 'pipe', stderr: 'pipe'})
  if (run.exitCode !== 0) throw new Error(`translation smoke failed (${run.exitCode}): ${new TextDecoder().decode(run.stdout).slice(-16000)}\n${new TextDecoder().decode(run.stderr)}`)
  const s = JSON.parse(readFileSync(join(dir, 'smoke.summary.json'), 'utf8'))
  if (s.replay !== 'default' || s.generated !== FAMILIES.length || Object.keys(s.families).length !== FAMILIES.length || !s.proven || s.findings || s.errors || s.falseRejections || s.unsafeVerdicts) throw new Error(`translation smoke coverage failed: ${JSON.stringify(s)}`)
  for (const tag of ['boolean', 'choice', 'number', 'record', 'optional', 'Map.get']) if (!s.acceptedTags[tag]) throw new Error(`translation smoke did not reach ${tag}`)
  console.log('TRANSLATION_SMOKE ' + JSON.stringify(s))
} finally { rmSync(dir, {recursive: true, force: true}) }
