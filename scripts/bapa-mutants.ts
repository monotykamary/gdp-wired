// Run only inside the supercomputer Lean job. Each malformed theorem must fail
// because its statement is false; BoundedMutants separately checks countermodels.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const out = process.env.SUPERCOMPUTER_OUTPUT_DIR!
const cases: Record<string, string> = {
  'instance-without-bound': 'example : (∀ k : Nat, k < 0 → False) → False := by intro h; exact h 0 (by omega)',
  'witness-without-bound': 'example : ∃ k : Nat, k < 0 ∧ True := by exact ⟨0, by omega, True.intro⟩',
  'inclusive-enumeration': 'example : allBelow (fun k => decide (k < 2)) 3 = true := by decide',
  'empty-exists': 'example : anyBelow (fun _ => true) 0 = true := by decide',
  'capture-witness': 'example : evalC (upd (fun _ => 0) 1 1) (fun _ _ => 0) (.eq (.var 1) (.const 0)) = true := by decide',
  'overlap-twice': 'example : card (fun _ => true) 1 = card (fun _ => true && true) 1 + card (fun _ => true) 1 := by decide',
}
mkdirSync(join(out, 'mutants'), {recursive: true})
for (const [name, body] of Object.entries(cases)) {
  const source = join(out, 'mutants', `${name}.lean`)
  writeFileSync(source, `import Bounded\nopen Kern Kern.Bounded\n${body}\n`)
  const result = Bun.spawnSync(['lean', source], {stdout: 'pipe', stderr: 'pipe'})
  const log = new TextDecoder().decode(result.stdout) + new TextDecoder().decode(result.stderr)
  writeFileSync(join(out, 'mutants', `${name}.log`), log)
  if (result.exitCode === 0 || !log.includes('error:') || /unknown (identifier|module)|unexpected token|file not found/.test(log)) {
    throw new Error(`${name}: expected a semantic theorem refusal, got exit ${result.exitCode}: ${log}`)
  }
}
writeFileSync(join(out, 'mutants.json'), JSON.stringify({refused: Object.keys(cases)}, null, 2) + '\n')
