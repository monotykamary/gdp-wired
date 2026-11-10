// Each mutation runs alone in the disposable Boat checkout and is restored exactly.
import {readFileSync, writeFileSync} from 'node:fs'
import {sourceDiagnostic} from '../../core/source-diagnostic.ts'
const cases = [
  {name: 'native-law-evaluation-off', file: 'core/source-check.ts', old: 'holds = law.evaluate(observation)', replacement: 'holds = true'},
  {name: 'unchecked-can-prove', file: 'core/source-check.ts', old: '({...verdict, proven: false, checked: false, kernelProven: verdict.proven && verdict.checked, translation:', replacement: '({...verdict, kernelProven: verdict.proven && verdict.checked, translation:'},
  {name: 'finite-enumeration-off', file: 'core/extract-check.ts', old: 'if (exhaustive && journal.enabled && !journal.reason)', replacement: 'if (false && exhaustive && journal.enabled && !journal.reason)'},
  {name: 'undefined-erased-to-zero', file: 'core/source-check.ts', old: "if (value === null || typeof value !== 'object') return value", replacement: "if (value === undefined) return 0; if (value === null || typeof value !== 'object') return value"},
  {name: 'source-copy-marker-lost', file: 'core/source-check.ts', old: 'if (marked(from)) mark(to)', replacement: 'if (false && marked(from)) mark(to)'},
]
const rows = []
for (const c of cases) {
  const original = readFileSync(c.file, 'utf8')
  if (original.split(c.old).length !== 2) throw new Error(`${c.name}: mutation anchor must match exactly once`)
  try {
    writeFileSync(c.file, original.replace(c.old, c.replacement))
    const result = Bun.spawnSync(['timeout', '90', 'bun', 'test', 'core/source-check.test.ts', '--timeout', '60000'], {stdout: 'pipe', stderr: 'pipe'})
    const output = new TextDecoder().decode(result.stdout) + new TextDecoder().decode(result.stderr)
    const caught = result.exitCode !== 0 && result.exitCode !== 124 && output.includes('(fail)') && !/SyntaxError|Module not found|Cannot find module/.test(output)
    rows.push({name: c.name, caught, exit: result.exitCode, failures: output.split('\n').filter(l => l.includes('(fail)'))})
    console.log(JSON.stringify(rows.at(-1)))
  } finally { writeFileSync(c.file, original) }
  if (readFileSync(c.file, 'utf8') !== original) throw new Error(`${c.name}: restoration failed`)
}
const report = {passed: rows.every(r => r.caught), mutants: rows}
if (process.argv[2]) writeFileSync(process.argv[2], JSON.stringify(sourceDiagnostic(report), null, 2) + '\n')
console.log('CROSSCHECK_MUTANTS ' + JSON.stringify(report))
if (!report.passed) process.exitCode = 1
