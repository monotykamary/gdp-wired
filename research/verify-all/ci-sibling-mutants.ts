// Disposable Boat checkout only; all mutations must be restored.
import {readFileSync} from 'node:fs'
import {checkMutations} from '../../core/mutate.ts'
const files = ['core/laws.ts', 'core/extract-shapes.ts', 'core/extract-read.ts']
const before = new Map(files.map(path => [path, readFileSync(path, 'utf8')]))
const binding = "  // An explicit binding is authoritative even when a name has only one owner.\n  if (l.method && [...probe.methods].some(method => method !== l.method)) throw new LawError(`the law is bound to ${l.method}, but reads a value belonging to ${[...probe.methods].join(', ')}`)\n  const method = l.method ?? (probe.methods.size === 1 ? [...probe.methods][0] : undefined)"
const result = checkMutations({
  lawSuite: 'siblings', timeoutMs: 120000,
  suites: [{name: 'siblings', command: ['bun', 'test', 'core/extract-ci-method-scope.test.ts', 'core/extract-ci-composite-optional.test.ts', 'core/extract-ci-lazy-identity.test.ts', 'core/extract-ci-lazy-key.test.ts']}],
  mutants: [
    {file: 'core/laws.ts', name: 'N1-silent-method-rebinding', from: binding, to: '  const method = probe.methods.size === 1 ? [...probe.methods][0] : l.method', bug: 'explicit method is overwritten by a field owner'},
    {file: 'core/laws.ts', name: 'B1-nested-optional-erased', from: 'operand => val(operand, {...c, strictOptional: true}, names, dry)', to: 'go', bug: 'nested arithmetic loses optional provenance'},
    {file: 'core/extract-shapes.ts', name: 'P2-lazy-argument-root-shared', from: 'const root: LazyRoot = [prefix, ordinal]', to: 'const root: LazyRoot = [prefix, 0]', bug: 'lazy fields alias across argument identities'},
    {file: 'core/extract-read.ts', name: 'P2-lazy-key-concatenated', from: 'JSON.stringify([record.root ?? [record.prefix, 0], [field]])', to: '`${record.prefix}${field}`', bug: 'field spelling collides with argument display prefix'},
    {file: 'core/extract-shapes.ts', name: 'P2-lazy-event-key-unbound', from: 'const key = disc && lazyKey(lazy, disc)', to: 'const key = disc && JSON.stringify([prefix, disc])', bug: 'synthetic selection no longer resolves by the structured field identity'},
  ],
})
console.log(result.markdown)
for (const row of result.rows) console.log(JSON.stringify({name: row.mutant, status: row.suites.siblings!.status, exit: row.suites.siblings!.exit, output: row.suites.siblings!.output}))
if (!result.passed) throw Error('a sibling mutant survived or errored')
for (const [file, text] of before) if (readFileSync(file, 'utf8') !== text) throw Error(`mutation not restored: ${file}`)
console.log('CI_SIBLING_MUTANTS_PASS restored=true')
