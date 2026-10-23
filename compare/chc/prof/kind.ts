// Not a solver: whether a task's law is k-inductive, `bun compare/chc/prof/kind.ts <task.smt2> [--ms 50000]` (`--tools
// kind` in modal_chc.py). For k = 1, 2, ...: the kernel's k-step goal (kernel.ts's stepLawObligations) with the law at
// each of the k states and the rule's kinds assumed, the law after them refuted, asked of the CDCL search for a model
// alone (core/bmc.ts's engine). Refuted: the law holds after any k states where it held, so from the start (with no
// run of fewer than k steps breaking it, which bounded runs decide) it always holds. That is k-induction's verdict,
// which the kernel doesn't check as it stands (its proofs are 1-inductive), so this only measures what it would add.
// Prints one JSON line: {answer: 'kinductive' | 'unknown', k, depths}.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build} from '../translate.ts'
import type {C, E} from '../../../core/machine.ts'
import {stepLawObligations, substC} from '../../../kernel/kernel.ts'
import {REFUTED, growCdcl} from '../../../kernel/cdcl.ts'
import {findBoundedRun} from '../../../core/bmc.ts'

const args = process.argv.slice(2), file = args[0]!
const ms = Number(args[args.indexOf('--ms') + 1] ?? 50_000) || 50_000, t0 = performance.now(), wall = t0 + ms
const b = build(parseChc(readFileSync(file, 'utf8'))), m = b.rule.machine, law = b.law
const after = {vars: Object.fromEntries(Object.keys(m.state).map(n => [n, {op: 'var', name: `${n}'`} as E])), maps: {}, flags: {}}
const depths: [number, string, number][] = []
let answer = 'unknown', at = 0
for (let k = 1; k <= 64 && performance.now() < wall; k++) {
  const t = performance.now()
  const g = stepLawObligations(m, b.rule.kindLaws(), {}, {name: 'k-induction', when: Array.from({length: k}, (): C => law.holds), then: substC(law.holds, after), steps: k})[0]!
  const out = growCdcl({name: `k-induction ${k}`, hyps: g.hyps}, new Map(), {nodes: 0}, {model: true, wall})
  if ('tree' in out || out.why === REFUTED) { depths.push([k, 'r', Math.round(performance.now() - t)]); answer = 'kinductive'; at = k; break }
  depths.push([k, out.stuck[0]!, Math.round(performance.now() - t)])
  if (out.stuck === 'unknown') break
}
// A k-inductive law whose runs of fewer than k steps all keep it holds; one such run that breaks it is a counterexample.
const short = answer === 'kinductive' && at > 1 ? findBoundedRun(m, [law], {ms: 1e9, wall: performance.now() + 5000, depth: at - 1}) : undefined
console.log(JSON.stringify({task: file, ms: Math.round(performance.now() - t0), stage: 'answer', answer: short ? 'unsat' : answer, k: at, depths}))
