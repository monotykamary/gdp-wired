// A task's k-induction certificate as Lean (KInd.lean's kind_sound): `bun compare/chc/prof/kind-lean.ts <task.smt2>
// [--ms 50000] > Task.lean`, then `lean Task.lean` beside the twin's .olean files (lean-kernel/). The search is
// core/kind.ts's, as compare/chc/kind.ts runs it; the theorem `<id>_kind_holds`: the law (error never reached) holds
// in every reachable state of the task's rule.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build} from '../translate.ts'
import {toLean} from '../../../lean-kernel/emit.ts'

const args = process.argv.slice(2), file = args[0]!, i = args.indexOf('--ms'), ms = i < 0 ? 50_000 : Number(args[i + 1])
const b = build(parseChc(readFileSync(file, 'utf8')))
console.log(toLean([{id: 'task', kInduction: {machine: b.rule.machine, laws: b.rule.kindLaws(), law: b.law, ms}}], {title: `k-induction for ${file.split('/').slice(-3).join('/').replace(/\/-|-\//g, x => x.split('').join(' '))}`}))
