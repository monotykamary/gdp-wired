// The axiom gate: what a run of `lean` printed, read against the files it ran. It fails the run where a theorem rests on
// an axiom past Lean's standard three (propext, Classical.choice, Quot.sound), where any declaration uses sorry, or where
// a `#print axioms` the files ask for went unanswered (a gate that reads nothing passes nothing). With GDP_LEAN_NATIVE=1
// (emit.ts's native_decide, asked for by a suite's --native run) the compiler's axioms are allowed too: Lean.ofReduceBool,
// Lean.trustCompiler and each check's own `…native_decide.ax_…`; a release's proofs never are.
//   bun scripts/lean-gate/gate.ts <lean's output> <file.lean>...     exit 0, or 1 with each reason on stdout
// scripts/lean-gate/lean runs lean through it: the Lean jobs put that directory first on their PATH.
import {readFileSync} from 'node:fs'

export const standard = ['propext', 'Classical.choice', 'Quot.sound']
const nativeAxiom = (a: string) => a === 'Lean.ofReduceBool' || a === 'Lean.trustCompiler' || /native_decide\.ax_/.test(a)

// Each `#print axioms` a file asks for (at a line's start, outside comments).
export function asked(source: string): string[] {
  const code = source.replace(/\/-[\s\S]*?-\//g, '').replace(/--.*$/gm, '')
  return [...code.matchAll(/^#print axioms\s+(\S+)/gm)].map(m => m[1]!)
}
// What lean answered: each theorem with its axioms (none for "does not depend on any axioms"). A long list may wrap.
export function answers(out: string): {name: string, axioms: string[]}[] {
  const deps = [...out.matchAll(/'([^']+)' depends on axioms: \[([^\]]*)\]/g)].map(m => ({name: m[1]!, axioms: m[2]!.split(',').map(a => a.trim()).filter(Boolean)}))
  const none = [...out.matchAll(/'([^']+)' does not depend on any axioms/g)].map(m => ({name: m[1]!, axioms: []}))
  return [...deps, ...none]
}
export function gate(out: string, sources: string[], native = false): string[] {
  const why: string[] = []
  if (/declaration uses 'sorry'/.test(out)) why.push("a declaration uses 'sorry'")
  for (const a of answers(out)) {
    const extra = a.axioms.filter(x => !standard.includes(x) && !(native && nativeAxiom(x)))
    if (extra.length) why.push(`${a.name} depends on ${extra.join(', ')}`)
  }
  const want = sources.flatMap(asked).length, got = answers(out).length
  if (got < want) why.push(`${want} #print axioms asked, ${got} answered`)
  return why
}

if (import.meta.main) {
  const [log, ...files] = process.argv.slice(2)
  if (!log) { console.log('usage: bun scripts/lean-gate/gate.ts <lean output> <file.lean>...'); process.exit(2) }
  const why = gate(readFileSync(log, 'utf8'), files.map(f => { try { return readFileSync(f, 'utf8') } catch { return '' } }), process.env.GDP_LEAN_NATIVE === '1')
  for (const w of why) console.log(`axiom-gate: ${w}`)
  process.exit(why.length ? 1 : 0)
}
