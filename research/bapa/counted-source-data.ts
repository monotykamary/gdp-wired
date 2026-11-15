// Data only: these definitions do not establish a source-to-producer bridge.
import type {Machine} from '../../core/machine.ts'
import {boundOf, postName, witnessesOf} from '../../kernel/kernel.ts'
import {retainedCMachineToLean} from '../../lean-kernel/emit.ts'
import {alphaProposals,rowAlphaProposals} from './source-projection.ts'
import {lawCoverage, type FamilyBundle} from './proof-capture.ts'

export function countedSourceDefinitions(id: string, bundle: FamilyBundle) {
  if (bundle.schema !== 'bapa-family/v1' || bundle.route !== 'counted-family' || !bundle.verdict.proven || !bundle.verdict.checked)
    throw Error('counted source requires a checked counted family')
  const source = bundle.original.machine, laws = bundle.original.laws, producer = bundle.final.machine
  if (source.history || (source.sums && Object.keys(source.sums).length) || Object.keys(source.fns ?? {}).length)
    throw Error('source history/sums/functions require a separate route')
  if (!laws.length || laws.some(l => l.stated !== undefined || l.some !== undefined || l.ex !== undefined || l.finite !== undefined || l.witness !== undefined))
    throw Error('source public laws require ordinary law metadata')
  const indices = lawCoverage(laws, bundle.final.laws)
  const rs = alphaProposals(source, producer), rows = rowAlphaProposals(source, producer)
  const vars = new Set<string>([...source.params, ...source.inputs, ...Object.keys(source.state), ...Object.keys(source.step.state ?? {})])
  const maps = new Set<string>([...Object.keys(source.maps ?? {}), ...Object.keys(source.step.maps ?? {}), ...(source.inputMaps ?? [])])
  // Expressions have the same var/get constructors consumed by leanTerms.
  const visit = (value: unknown): void => {
    if (!value || typeof value !== 'object') return
    if (Array.isArray(value)) { value.forEach(visit); return }
    const node = value as Record<string, unknown>
    if (node.op === 'var' && typeof node.name === 'string') vars.add(node.name)
    if (node.op === 'get' && typeof node.map === 'string') maps.add(node.map)
    Object.values(node).forEach(visit)
  }
  visit(source); visit(laws)
  for (const [flag, q] of Object.entries(source.step.flags ?? {})) {
    vars.add(`?${flag}`)
    if (q.op === 'all') { boundOf(q).forEach(v => vars.add(v)); witnessesOf(flag, q).forEach(v => vars.add(v)) }
  }
  for (const w of Object.values(source.step.maps ?? {})) if ('each' in w) vars.add(w.each)
  for (const l of [...laws, ...(source.facts ?? [])]) {
    if (l.forall) vars.add(l.forall)
    for (const k of l.keys ?? []) vars.add(k)
  }
  const counts = Object.entries(source.counts ?? {})
  for (const [name, d] of counts) {
    maps.add(name); maps.add(postName(name)); vars.add(d.j); vars.add(d.key); vars.add(d.lo ?? d.j)
  }
  for (const r of rs) { vars.add(`?${r.flag}`); vars.add(r.old); vars.add(r.fresh) }
  let sourceDefs = '', newCountMapIndices: number[] = []
  const normalized: Machine = {...source, counts: undefined, inputMaps: [...(source.inputMaps ?? []), ...counts.map(([name]) => name)]}
  const producerText = retainedCMachineToLean(id, producer, bundle.final.laws, bundle.final.proof, {
    extraVars: [...vars], extraMaps: [...maps], after: basis => {
      const {ix, mx} = basis
      newCountMapIndices = Object.keys(producer.counts ?? {}).filter(name => !Object.hasOwn(source.counts ?? {}, name)).map(mx)
      const renames = rs.map(r => `⟨${ix(`?${r.flag}`)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
      const rowRenames = rows.map(r => `⟨${mx(r.map)}, ${ix(r.old)}, ${ix(r.fresh)}⟩`).join(', ')
      const claims = laws.map((law, j) => `def ${id}_source_law${j} : MLaw := ⟨${basis.condition(law.holds)}, ${law.forall ? `some ${ix(law.forall)}` : 'none'}⟩\ndef ${id}_source_keys${j} : List Nat := [${(law.keys ?? []).map(ix).join(', ')}]`).join('\n')
      sourceDefs = `-- Proposed check only: RowAlpha.renameAll (QAlpha.renameAll ${id}_source ${id}_source_renames) ${id}_source_row_renames = { ${id}_machine with carried := ${id}_source.carried }
def ${id}_source : SMachine := ${basis.machine(normalized)}\ndef ${id}_source_decls : List CDecl := ${basis.decls(source.counts)}\ndef ${id}_source_renames : List QAlpha.Rename := [${renames}]\ndef ${id}_source_row_renames : List RowAlpha.Rename := [${rowRenames}]\ndef ${id}_source_count_maps : List Nat := [${newCountMapIndices.join(', ')}]\ndef ${id}_source_law_indices : List Nat := [${indices.join(', ')}]\n${claims}`
      return ''
    }
  })
  return {producerText, sourceDefs, publicLawIndices: indices, newCountMapIndices}
}
