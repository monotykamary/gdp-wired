import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

// A discarded observation at the existing allocation expression. No new cap,
// loop, helper dispatch, RNG call, sort, early return or result-field mutation.
export function applyRequestAccounting(root: string) {
  const path = join(root, 'core/infer.ts'), source = readFileSync(path, 'utf8')
  const before = 'for (const [i, d] of doms) combos = combos.flatMap(c => d.map(v2 => ({...c, [i]: v2})))'
  const after = 'for (const [i, d] of doms) combos = combos.flatMap(c => d.map(v2 => (coreMeter.tableCells += Object.keys(c).length + 1, {...c, [i]: v2})))'
  assert.equal(source.split(before).length, 2, 'one original request-product expression')
  writeFileSync(path, source.replace(before, after))
  const template = readFileSync('request-input/request-materialization.test.source', 'utf8')
  assert.equal(template.split('__BASELINE_STATEMENT__').length, 2)
  writeFileSync(join(root, 'core/request-materialization.test.ts'), template.replace('__BASELINE_STATEMENT__', JSON.stringify(before)))
  const roster = join(root, 'scripts/test-shards.ts'), text = readFileSync(roster, 'utf8'), anchor = 'meter-complete.test.ts'
  assert.equal(text.split(anchor).length, 2)
  writeFileSync(roster, text.replace(anchor, anchor + ' request-materialization.test.ts'))
}
