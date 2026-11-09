// Disposable checkout only: bun research/verify-all/ci-audit-mutants.ts
import {readFileSync} from 'node:fs'
import {checkMutations} from '../../core/mutate.ts'

const file = 'core/laws.ts'
const guard = "  if ([later, earlier].some(v => v.t === 'opt')) throw new LawError(c.strictOptional ? 'arithmetic on an optional standalone value is not supported' : 'arithmetic on an optional value is not supported in calendar comparisons')"
const before = readFileSync(file, 'utf8')
const result = checkMutations({
  lawSuite: 'audit', timeoutMs: 120_000,
  suites: [{name: 'audit', command: ['bun', 'test', 'core/extract-ci-audit.test.ts']}],
  mutants: [
    {file, name: 'B1-standalone-only-guard', from: guard, to: guard.replace('if ([', 'if (c.strictOptional && ['), bug: 'optional class result bypasses calendar arithmetic guard'},
  ],
})
console.log(result.markdown)
for (const row of result.rows) {
  console.log(JSON.stringify({mutant: row.mutant, status: row.suites.audit!.status, exit: row.suites.audit!.exit}))
  console.log(row.suites.audit!.output)
}
if (!result.passed) throw new Error('an audit mutant survived or errored')
if (readFileSync(file, 'utf8') !== before) throw new Error('mutation runner did not restore source')
console.log('CI_AUDIT_MUTATIONS_PASS restored=true')
