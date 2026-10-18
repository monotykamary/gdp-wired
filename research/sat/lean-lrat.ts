// The optional Lean path for a refutation: the CNF as Lean data and our LRAT proof as text, checked by Lean's own LRAT
// checker (Std.Tactic.BVDecide.LRAT.check, the one bv_decide uses), whose `check_sound` gives `cnf.Unsat`.
// `bun lean-lrat.ts <name regex> <out dir> [kernel|native]`: kernel reduces the check with `decide +kernel` (no axiom
// beyond Lean's three), native runs it compiled (`native_decide`, which adds `Lean.ofReduceBool`, as bv_decide does).
import {appendFileSync, mkdirSync, writeFileSync} from 'node:fs'
import {problems} from './bench.ts'
import {solve} from './solver.ts'

const [pattern = 'PHP\\(6', out = '.', how = 'kernel'] = process.argv.slice(2)
mkdirSync(out, {recursive: true})
for (const [name, make] of problems) {
  if (!new RegExp(pattern).test(name)) continue
  const {vars, cnf} = make()
  const r = solve(vars, cnf)
  if (r.kind !== 'unsat') { console.log(`${name}: ${r.kind}, nothing to certify`); continue }
  // Lean's variables start at 0; its LRAT checker numbers them from 1 again, so the proof's literals stay as they are.
  const clause = (c: number[]) => `[${c.map(l => `(${Math.abs(l) - 1}, ${l > 0})`).join(', ')}]`
  // Lean's checker ignores the ids written and appends each lemma as the next clause, so ids are renumbered to run on
  // from the input's (trimming leaves gaps).
  const ids = new Map<number, number>()
  for (const s of r.lrat) if ('id' in s) ids.set(s.id, cnf.length + 1 + ids.size)
  const id = (h: number) => ids.get(h) ?? h
  const line = (s: (typeof r.lrat)[number]) => ('del' in s ? `1 d ${[...s.del.map(id), 0].join(' ')}` : `${id(s.id)} ${[...s.clause, 0].join(' ')} ${[...s.hints.map(id), 0].join(' ')}`)
  // The certificate goes in its own file, written in chunks (a 10-bit multiplier's is hundreds of MB), and a tampered
  // copy Lean must reject: the last hint of the last lemma (the empty clause's conflict) dropped.
  const file = name.replace(/[^A-Za-z0-9]+/g, '_').replace(/^_|_$/g, '')
  const last = r.lrat.at(-1)!
  const write = (path: string, steps: typeof r.lrat) => {
    writeFileSync(path, '')
    for (let i = 0; i < steps.length; i += 10000) appendFileSync(path, steps.slice(i, i + 10000).map(line).join('\n') + '\n')
  }
  write(`${out}/${file}.lrat`, r.lrat)
  write(`${out}/${file}.tampered.lrat`, [...r.lrat.slice(0, -1), 'id' in last ? {...last, hints: last.hints.slice(0, -1)} : last])
  writeFileSync(`${out}/${file}.lean`, `import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser
open Std.Sat Std.Tactic.BVDecide
set_option maxRecDepth 100000

-- ${name}: ${vars} variables, ${cnf.length} clauses; ${r.lrat.length} proof steps from gdp-wired/sat/solver.ts
def cnf : CNF Nat := ⟨#[${cnf.map(clause).join(',\n  ')}]⟩

def cert : String := include_str "${file}.lrat"

def parse (s : String) : Array LRAT.IntAction := match LRAT.parseLRATProof s.toUTF8 with
  | .ok p => p
  | .error _ => #[]
def proof : Array LRAT.IntAction := parse cert
def tampered : String := include_str "${file}.tampered.lrat"

${how === 'kernel' ? 'set_option maxHeartbeats 0 in\n' : ''}theorem unsat : cnf.Unsat := LRAT.check_sound proof cnf (by ${how === 'kernel' ? 'decide +kernel' : 'native_decide'})

#print axioms unsat

${how === 'kernel' ? 'set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n' : ''}example : LRAT.check (parse tampered) cnf = false := by ${how === 'kernel' ? 'decide +kernel' : 'native_decide'}
`)
  console.log(`${out}/${file}.lean: ${r.lrat.length} steps`)
}
