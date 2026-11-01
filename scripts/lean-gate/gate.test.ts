// The axiom gate (gate.ts) on lean's own words, and every Lean job going through it: supercomputer/suite.json's, the
// interchange's (interchange/lean-jobs.ts) and the bar's (gates/bar.ts).
import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {asked, gate} from './gate.ts'

const root = join(import.meta.dir, '..', '..')
const std = (n: string) => `'${n}' depends on axioms: [propext, Classical.choice, Quot.sound]`
const src = '/-! #print axioms skipped -/\ntheorem a : True := trivial\ntheorem b : True := trivial\n-- #print axioms c\n#print axioms a\n#print axioms b\n'

test('the standard axioms pass; another axiom, sorry or an unanswered #print fail', () => {
  expect(asked(src)).toEqual(['a', 'b'])
  expect(gate(`${std('a')}\n'b' does not depend on any axioms\n`, [src])).toEqual([])
  expect(gate(`${std('a')}\n'b' depends on axioms: [propext, planted]\n`, [src])).toEqual(['b depends on planted'])
  expect(gate(`${std('a')}\n'b' depends on axioms: [propext, sorryAx]\n`, [src])).toEqual(['b depends on sorryAx'])
  expect(gate(`X.lean:3:8: warning: declaration uses 'sorry'\n${std('a')}\n${std('b')}\n`, [src])).toEqual(["a declaration uses 'sorry'"])
  expect(gate(std('a'), [src])).toEqual(['2 #print axioms asked, 1 answered'])
  // A list that wraps, and the compiler's axioms only where native_decide was asked for.
  const native = `'a' depends on axioms: [propext,\n Classical.choice,\n Lean.ofReduceBool,\n a._native.native_decide.ax_1_1]\n${std('b')}`
  expect(gate(native, [src])).toEqual(['a depends on Lean.ofReduceBool, a._native.native_decide.ax_1_1'])
  expect(gate(native, [src], true)).toEqual([])
})

type Job = {name: string, cmd: string, cwd?: string}
const gated = (j: Job) => /export PATH=\$PWD(\/\.\.)?\/scripts\/lean-gate:\$PATH; /.test(j.cmd) || /scripts\/lean-gate\/gate\.ts lake\.out/.test(j.cmd)
test('every job that runs lean or lake goes through the gate', () => {
  const suite = JSON.parse(readFileSync(join(root, 'supercomputer', 'suite.json'), 'utf8')) as Job[]
  const lean = suite.filter(j => /\blean\b|\blake build\b|lean-items\.sh|lean-data\.sh|lean-edges\.sh/.test(j.cmd))
  expect(lean.length).toBeGreaterThan(60)
  expect(lean.filter(j => !gated(j)).map(j => j.name)).toEqual([])
  // (the prefix names the directory from the job's own cwd)
  for (const j of lean.filter(x => x.cmd.startsWith('export PATH='))) expect(j.cmd.startsWith(j.cwd === 'lean-kernel' ? 'export PATH=$PWD/..' : 'export PATH=$PWD/scripts')).toBe(true)
  expect(readFileSync(join(root, 'interchange', 'lean-jobs.ts'), 'utf8')).toContain("'export PATH=$PWD/scripts/lean-gate:$PATH; cd lean-kernel")
  expect(readFileSync(join(root, 'gates', 'bar.ts'), 'utf8')).toContain("const pre = 'export PATH=$PWD/../scripts/lean-gate:$PATH; ")
})
