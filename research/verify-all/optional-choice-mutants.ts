// Run only in a disposable checkout: bun research/verify-all/optional-choice-mutants.ts
// The designated suite must pass unmodified and kill each runtime mutation.
import {readFileSync} from 'node:fs'
import {checkMutations} from '../../core/mutate.ts'

const file = 'core/laws.ts', source = readFileSync(file, 'utf8')
const eq = "compare('==', av, bv, e, strictOptional)"
const ordered = 'compare(op, av, bv, e, strictOptional)'
const start = source.indexOf('      const equal = any(absent,')
const end = source.indexOf('\n  const un =', start)
if (start < 0 || end < start) throw Error('optional comparison block not found')
const block = source.slice(start, end)
const calendar = "  if ([later, earlier].some(v => v.t === 'opt')) throw new LawError(c.strictOptional ? 'arithmetic on an optional standalone value is not supported' : 'arithmetic on an optional value is not supported in calendar comparisons')"
const result = checkMutations({
  lawSuite: 'source-laws', timeoutMs: 120_000,
  suites: [{name: 'source-laws', command: ['bun', 'test', 'core/extract-standalone.test.ts', '--test-name-pattern', 'optional choice law|optional standalone calendar']}],
  mutants: [
    {file, name: 'drop-equality-context', from: eq, to: "compare('==', av, bv, e)", bug: 'present choices compared by local indices'},
    {file, name: 'drop-both-recursive-contexts', from: block, to: block.replace(eq, "compare('==', av, bv, e)").replace(ordered, 'compare(op, av, bv, e)'), bug: 'original recursive context loss'},
    {file, name: 'drop-calendar-optional-guard', from: calendar, to: '  // mutant: ignore optional calendar operands', bug: 'calendar helper unwraps absent scalar'},
  ],
})
console.log(result.markdown)
for (const row of result.rows) {
  console.log(JSON.stringify({mutant: row.mutant, status: row.suites['source-laws']!.status, exit: row.suites['source-laws']!.exit}))
  console.log(row.suites['source-laws']!.output)
}
if (!result.passed) throw Error('a source-law mutant survived or errored')
if (readFileSync(file, 'utf8') !== source) throw Error('mutation runner did not restore source')
console.log('MUTATIONS_PASS restored=true')
