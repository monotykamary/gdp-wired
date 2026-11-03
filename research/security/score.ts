// Benchmark admission is deliberately stricter than a search finding a model.
type Claim = {name: string, expr: string, verdict: string, run?: string[], replayed?: string}
export type RecallSide = {version: string, status: string, result?: {rules: {ok: boolean, entry?: string, laws: Claim[]}[]}}
export function scoreRecall(sides: RecallSide[], training = false): {found: boolean, reason: string} {
  const before = sides.find(s => s.version === 'vulnerable'), after = sides.find(s => s.version === 'fixed')
  if (training) {
    const found = !!before?.result && before.result.rules.every(r => r.ok) && before.result.rules.some(r => r.laws.some(l => l.verdict === 'broken' && l.run?.length && l.replayed))
    return {found, reason: found ? 'training flaw reproduced on original code' : 'training flaw not reproduced on original code'}
  }
  if (!before?.result || !after?.result) return {found: false, reason: 'both original revisions required'}
  if ([before, after].some(s => s.result!.rules.some(r => !r.ok))) return {found: false, reason: 'reader refused an original revision'}
  // Only stated laws count, never --security candidates. Replay must explicitly name the original
  // reproduction; an environment-model schedule alone does not meet this bar.
  const claims = (s: RecallSide) => s.result!.rules.flatMap(r => r.laws.map(l => ({...l, entry: r.entry})))
  const broken = claims(before).filter(l => l.verdict === 'broken' && l.run?.length && l.replayed)
  const fixed = claims(after)
  const found = broken.some(b => fixed.some(f => f.entry === b.entry && f.name === b.name && f.expr === b.expr && ['proven', 'unknown'].includes(f.verdict)))
  return {found, reason: found ? 'stated law, original replay, fixed not refuted' : 'no stated law with original replay and checked fixed counterpart'}
}
