// The existential examples' Lean export, and two tampered copies Lean must refuse (the suite's lean-exists job):
// `bun exists-tamper.ts <dir>` writes Exists.lean (examples/exists.ts's laws, each stated as ∃), ExistsGhost.lean
// (the evens counter's ghost witness moved by 2 a step, where the law needs 1: the machine's check fails) and
// ExistsTerm.lean (the window's witness hi + 1 in place of lo: its substitution is not the law the kernel proved).
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {toLean} from './emit.ts'
import {leanItems} from '../examples/exists.ts'

const dir = process.argv[2] ?? '.', text = toLean(leanItems(), {title: 'there exists'})
const swap = (from: RegExp, to: string) => { if (!from.test(text)) throw new Error(`no ${from} in the export`); return text.replace(from, to) }
writeFileSync(join(dir, 'Exists.lean'), text)
writeFileSync(join(dir, 'ExistsGhost.lean'), swap(/(\(2, \.const 0, \.ite \(\.eq \(\.var 0\) \(\.const 0\)\) \(\.add \(\.var 2\) \(\.const )1\)\)/, '$12))'))
writeFileSync(join(dir, 'ExistsTerm.lean'), text.replaceAll('substC [(5, .var 2)]', 'substC [(5, .add (.var 3) (.const 1))]').replaceAll('applyS [(5, .var 2)]', 'applyS [(5, .add (.var 3) (.const 1))]').replaceAll('some_of_subst [(5, .var 2)]', 'some_of_subst [(5, .add (.var 3) (.const 1))]'))
console.log('wrote Exists.lean, ExistsGhost.lean, ExistsTerm.lean')
