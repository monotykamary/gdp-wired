import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const blob = (text: string) => createHash('sha1').update('blob ' + Buffer.byteLength(text) + '\0').update(text).digest('hex')
export function applyBudgetFiniteness(root: string) {
  const path = join(root, 'kernel/prove.ts')
  let source = readFileSync(path, 'utf8')
  assert.equal(blob(source), 'a804a742828799b75c9537b9f238338f250b6093', 'exact request-source work clock')
  const replace = (before: string, after: string) => { assert.equal(source.split(before).length, 2); source = source.replace(before, after) }
  replace('  if (budgetUnitsEnd !== undefined && fullWork() > budgetUnitsEnd) throw new BudgetExpired(phase)',
    '  if (budgetUnitsEnd !== undefined) {\n    const used = fullWork()\n    if (!Number.isFinite(used) || used > budgetUnitsEnd) throw new BudgetExpired(phase)\n  }')
  replace('    const previous = budgetUnitsEnd\n    budgetUnitsEnd = Math.min(previous ?? Infinity, workCap, fullWork() + units)',
    '    const previous = budgetUnitsEnd, used = fullWork()\n    const end = Math.min(previous ?? Infinity, workCap, used + units)\n    if (!Number.isFinite(used) || !Number.isFinite(end)) throw new BudgetExpired(\'entry\')\n    budgetUnitsEnd = end')
  writeFileSync(path, source)
  writeFileSync(join(root, 'core/work-finiteness.test.ts'), readFileSync('numeric-input/work-finiteness.test.source'))
  const roster = join(root, 'scripts/test-shards.ts'), text = readFileSync(roster, 'utf8'), anchor = 'request-materialization.test.ts'
  assert.equal(blob(text), 'b69f6c1859ea585fcbd5d889e238b58187ed4621', 'exact request-source roster')
  assert.equal(text.split(anchor).length, 2)
  writeFileSync(roster, text.replace(anchor, anchor + ' work-finiteness.test.ts'))
}
