import {answers, standard} from '../axiom-audit.ts'

export const theorem = 'aggregate_claim'
export const axiomCommand = `\nset_option pp.fullNames true in\n#print axioms ${theorem}\n`
// Check the public theorem specifically, not just a count of #print answers.
// With fullNames on, no short-name alias for an arbitrary axiom is allowed.
export function exactAxioms(log: string): readonly string[] {
  const rows = answers(log)
  const row = rows[0]
  if (/\b(?:error|warning):[^\r\n]*(?:sorry|admit)|\berror:/i.test(log) || rows.length !== 1 || row?.name !== theorem
      || row.axioms.some(a => !standard.includes(a)) || new Set(row.axioms).size !== row.axioms.length)
    throw new Error('Lean did not report exactly the allowed axioms for the bound aggregate theorem.')
  return row.axioms
}
