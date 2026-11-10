import {strict as assert} from 'node:assert'
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'

// Only discarded additive observations: preserve the checker AST after erasure.
// tableCells includes examined/serialized UTF-16 key code units, not a fitted weight.
export function applyCanonicalization(root: string) {
  const path = join(root, 'kernel/kernel.ts')
  let source = readFileSync(path, 'utf8')
  const replace = (before: string, after: string) => { assert.equal(source.split(before).length, 2, before); source = source.replace(before, after) }
  replace('export const canon = (lin: Lin): string => {', 'export const canon = (lin: Lin): string => {\n  kernelMeter.tableCells += 1')
  replace('map(key => `${key}:${lin[key]}`)', 'map(key => (kernelMeter.tableCells += key.length + 1, `${key}:${lin[key]}`))')
  replace('export const canonFlip = (lin: Lin): string => {', 'export const canonFlip = (lin: Lin): string => {\n  kernelMeter.tableCells += 1')
  replace("for (const key of keys.sort()) { const c =", "for (const key of keys.sort()) { kernelMeter.tableCells += key.length + 1; const c =")
  replace('function decide(lin: Lin, path: Path): boolean | undefined {', 'function decide(lin: Lin, path: Path): boolean | undefined {\n  kernelMeter.tableCells += 1')
  replace('for (const key in lin) { if (!Number.isSafeInteger(lin[key]))', 'for (const key in lin) { kernelMeter.tableCells += key.length + 1; if (!Number.isSafeInteger(lin[key]))')
  replace('export function cellParts(cell: string): {map: string, key?: Lin, keys?: Lin[]} {', 'export function cellParts(cell: string): {map: string, key?: Lin, keys?: Lin[]} {\n  kernelMeter.tableCells += 1')
  replace('for (let i = 0; i <= text.length; i++) {\n    const ch = text[i]', 'for (let i = 0; i <= text.length; i++) {\n    kernelMeter.tableCells += 1\n    const ch = text[i]')
  replace("for (const part of splitOuter(text, ',')) if (part)", "for (const part of splitOuter(text, ',')) if ((kernelMeter.tableCells += part.length + 1, part))")
  writeFileSync(path, source)
  writeFileSync(join(root, 'kernel/canonical-meter.test.ts'), readFileSync('coverage-input/canonical-meter.test.source'))
  const roster = join(root, 'scripts/test-shards.ts'), text = readFileSync(roster, 'utf8'), anchor = 'work-budget.test.ts'
  assert.equal(text.split(anchor).length, 2)
  writeFileSync(roster, text.replace(anchor, anchor + ' canonical-meter.test.ts'))
}
