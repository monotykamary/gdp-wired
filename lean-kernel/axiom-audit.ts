// Pure audit of native Lean output. This is not a proof checker or a substitute
// for executing Lean; callers must bind the log to the exact generated sources.
export const standard = ['propext', 'Classical.choice', 'Quot.sound']
const nativeAxiom = (a: string) => a === 'Lean.ofReduceBool' || a === 'Lean.trustCompiler' || /native_decide\.ax_/.test(a)
export function asked(source: string): string[] {
  const code = source.replace(/\/-[\s\S]*?-\//g, '').replace(/--.*$/gm, '')
  return [...code.matchAll(/^#print axioms\s+(\S+)/gm)].map(m => m[1]!)
}
export function answers(out: string): {name: string, axioms: string[]}[] {
  const deps = [...out.matchAll(/^'([^\r\n]+)' depends on axioms: \[([^\]]*)\]\r?$/gm)].map(m => ({name: m[1]!, axioms: m[2]!.split(',').map(a => a.trim()).filter(Boolean)}))
  const none = [...out.matchAll(/^'([^\r\n]+)' does not depend on any axioms\r?$/gm)].map(m => ({name: m[1]!, axioms: []}))
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
export function auditLiftLog(out: string, sources: string[], required: string[], expectedAxioms?: Record<string, string[]>): {name: string, axioms: string[]}[] {
  if (!required.length || required.some(n => !/^[A-Za-z_][A-Za-z0-9_.']*$/.test(n)) || new Set(required).size !== required.length) throw Error('invalid or empty source theorem coverage')
  const errors = gate(out, sources, false)
  if (/\berror:/.test(out)) errors.push('Lean reported an error')
  const rows = answers(out), names = [...new Set([...sources.flatMap(asked), ...required])]
  for (const name of names) {
    const found = rows.filter(r => r.name === name)
    if (found.length !== 1) errors.push(`expected one axiom answer for ${name}, got ${found.length}`)
    const expected = expectedAxioms?.[name]
    if (expected && found.length === 1 && JSON.stringify([...expected].sort()) !== JSON.stringify([...found[0]!.axioms].sort())) errors.push(`axiom set changed for ${name}`)
  }
  if (expectedAxioms) for (const name of Object.keys(expectedAxioms)) if (!names.includes(name)) errors.push(`baseline theorem missing: ${name}`)
  if (errors.length) throw Error(errors.join('; '))
  return rows.filter(r => names.includes(r.name))
}
