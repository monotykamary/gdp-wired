// CLI compatibility wrapper around the product's pure axiom audit.
import {readFileSync} from 'node:fs'
import {gate} from '../../lean-kernel/axiom-audit.ts'
export {standard, asked, answers, gate} from '../../lean-kernel/axiom-audit.ts'

if (import.meta.main) {
  const [log, ...files] = process.argv.slice(2)
  if (!log) { console.log('usage: bun scripts/lean-gate/gate.ts <lean output> <file.lean>...'); process.exit(2) }
  const why = gate(readFileSync(log, 'utf8'), files.map(f => { try { return readFileSync(f, 'utf8') } catch { return '' } }), process.env.GDP_LEAN_NATIVE === '1')
  for (const w of why) console.log(`axiom-gate: ${w}`)
  process.exit(why.length ? 1 : 0)
}
