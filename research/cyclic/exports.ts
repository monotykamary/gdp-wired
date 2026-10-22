// The Lean export from cyclic certificates against the usual one: `bun research/cyclic/exports.ts <usual.lean>
// <cyclic.lean>` (two Proofs.lean files package-check.ts wrote for the same items, without and with GDP_CERT=cyclic).
// Each theorem a user cites (`<id>.lawN`, `<id>_stepN_holds`, `<id>_liveN_holds`, `<id>_liveN_holds_wf`, `<id>_halts`,
// `<id>_refines`, `<id>_laws`, `<id>_hlaws`, `<id>_orig_laws`, a corollary) is compared by its statement's text, and each
// definition a statement names (the machine, a history, a ghosted machine, a refinement, a loop, a fold, a liveness) by its
// text; a step law's SKStep by what SKStepHolds reads of it (its `when`s, `then`, the names of later requests and primed
// names, not the certificate in it). A statement over the laws as the usual proof's entries (`∀ e ∈ <id>_proof, e.Holds ρ
// M`, Sets.lean's SEntry.Holds being `holdsOver e.law M e.keys2 ρ`; a fold's `<id>_proof.map (·.1)`) is the cyclic
// export's over the same laws listed (`∀ e ∈ <id>_mlaws, holdsOver e.1 M e.2 ρ`, `<id>_flaws`): counted apart, as the same
// up to that list. Theorems about the certificate itself (a check, a node's, a law's own check) differ by construction.
import {readFileSync} from 'node:fs'

const [usualPath, cyclicPath] = process.argv.slice(2)
if (!usualPath || !cyclicPath) throw new Error('usage: bun research/cyclic/exports.ts <usual Proofs.lean> <cyclic Proofs.lean>')

type Decls = {theorems: Map<string, string>, defs: Map<string, string>}
function decls(path: string): Decls {
  const text = readFileSync(path, 'utf8'), theorems = new Map<string, string>(), defs = new Map<string, string>()
  let ns = ''
  const lines = text.split('\n')
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!
    const n = /^namespace (\S+)/.exec(line)
    if (n) { ns = `${n[1]}.`; continue }
    if (/^end /.test(line)) { ns = ''; continue }
    const t = /^theorem (\S+)(.*)$/.exec(line)
    if (t) {
      // The statement: up to the first `:=` (several lines at most).
      let body = t[2]!, j = i
      while (!body.includes(':=') && j + 1 < lines.length) body += `\n${lines[++j]}`
      theorems.set(`${ns}${t[1]}`, body.slice(0, body.indexOf(':=')).trim())
      continue
    }
    const d = /^(?:noncomputable )?def (\S+) : (\S+) := (.*)$/.exec(line)
    if (d) {
      let body = d[3]!, j = i
      while (j + 1 < lines.length && !/^(def|theorem|example|noncomputable|namespace|end|--|\/-|abbrev|$)/.test(lines[j + 1]!)) body += `\n${lines[++j]}`
      defs.set(`${ns}${d[1]}`, `${d[2]} := ${body}`)
    }
  }
  return {theorems, defs}
}
const u = decls(usualPath), c = decls(cyclicPath)
// A user-facing theorem: a law plainly, a step law's, a liveness's, a loop's, a history's, a ghost's, or a corollary
// (any theorem not about the certificate: the proof's entries, checks, nodes, a law's or a step law's own check).
const certificate = (name: string) => /_(check|hcheck|sound|values|ghostOk|node\d+_\w+|node\d+|law\d+_ok|law\d+_holds|step\d+_ok|live\d+_(ok|stay|cover|helps|allows)|allowed|lemma\d+|between\d+|facts_hold\w*|ok|rok|fn_eq)$/.test(name)
// The laws as the usual proof's entries, read as the cyclic export lists them.
const entries = (stmt: string) => stmt.replace(/∀ e ∈ (\S+)_proof, e\.Holds (\S+) (\S+)/g, '∀ e ∈ $1_mlaws, holdsOver e.1 $3 e.2 $2')
  .replace(/∀ e ∈ (\S+)_proof, avoids (\S+) e\.law\.holds = true → e\.Holds (\S+) (\S+)/g, '∀ e ∈ $1_mlaws, avoids $2 e.1.holds = true → holdsOver e.1 $4 e.2 $3')
  .replace(/(\S+)_proof\.map \(·\.1\)/g, '$1_flaws')
const kept = (name: string) => !certificate(name)
// What SKStepHolds reads of an SKStep: its first five fields (whens, then, ren, prime, primeMaps).
const skstepMeaning = (body: string) => body.split('\n').slice(0, 5).join('\n')
const out = {same: 0, sameUpToEntries: [] as string[], differ: [] as string[], onlyUsual: [] as string[], onlyCyclic: [] as string[], certificate: 0, defsSame: 0, defsDiffer: [] as string[]}
for (const [name, stmt] of u.theorems) {
  if (!kept(name)) { out.certificate++; continue }
  const other = c.theorems.get(name)
  if (other === undefined) out.onlyUsual.push(name)
  else if (other === stmt) out.same++
  else if (other === entries(stmt)) out.sameUpToEntries.push(name)
  else out.differ.push(name)
}
for (const name of c.theorems.keys()) if (kept(name) && !u.theorems.has(name)) out.onlyCyclic.push(name)
// The definitions the user-facing statements name.
const named = (name: string) => /_(machine|hist|ghosted|refined|loop|fold|live\d+|step\d+)$/.test(name)
for (const [name, body] of u.defs) {
  if (!named(name) || !c.defs.has(name)) continue
  const other = c.defs.get(name)!
  const same = /_step\d+$/.test(name) ? skstepMeaning(body) === skstepMeaning(other) : body === other
  if (same) out.defsSame++; else out.defsDiffer.push(name)
}
console.log(JSON.stringify({theorems: {usual: u.theorems.size, cyclic: c.theorems.size}, statements: {same: out.same, sameUpToEntries: out.sameUpToEntries, differ: out.differ, onlyUsual: out.onlyUsual, onlyCyclic: out.onlyCyclic},
  certificateTheorems: out.certificate, definitions: {same: out.defsSame, differ: out.defsDiffer}}, null, 1))
