// Benchmark admission is deliberately stricter than a search finding a model.
type Claim = {name: string, expr: string, verdict: string, run?: string[], replayed?: string}
type Rule = {ok: boolean, entry?: string, ctor?: string, laws: Claim[]}
export type RecallSide = {version: string, status: string, result?: {rules: Rule[]}}
const text = (value: string | undefined) => typeof value === 'string' && value.trim().length > 0
const ruleKey = (rule: Rule) => JSON.stringify([rule.entry, rule.ctor ?? null])
const claimKey = (rule: Rule, claim: Claim) => JSON.stringify([rule.entry, rule.ctor ?? null, claim.name, claim.expr])
const familyKey = (rule: Rule, claim: Claim) => JSON.stringify([rule.entry, claim.name, claim.expr])
function complete(side: RecallSide): boolean {
  if (!['checked', 'needs-reviewed-policy-and-original-replay'].includes(side.status) || !side.result?.rules.length) return false
  const rules = new Set<string>(), claims = new Set<string>()
  for (const rule of side.result.rules) {
    if (!rule.ok || !text(rule.entry) || (rule.ctor !== undefined && !text(rule.ctor)) || rules.has(ruleKey(rule))) return false
    rules.add(ruleKey(rule))
    for (const claim of rule.laws) {
      const key = claimKey(rule, claim)
      if (!text(claim.name) || !text(claim.expr) || !['proven', 'broken', 'unknown'].includes(claim.verdict) || claims.has(key)) return false
      claims.add(key)
    }
  }
  return true
}
const replayed = (claim: Claim) => claim.verdict === 'broken' && !!claim.run?.length && claim.run.every(text) && text(claim.replayed)
export function scoreRecall(sides: RecallSide[], training = false): {found: boolean, reason: string} {
  const versions = training ? ['vulnerable'] : ['vulnerable', 'fixed']
  if (sides.some(s => !versions.includes(s.version)) || new Set(sides.map(s => s.version)).size !== sides.length) {
    return {found: false, reason: 'duplicate or unexpected original revision'}
  }
  const before = sides.find(s => s.version === 'vulnerable'), after = sides.find(s => s.version === 'fixed')
  if (!before?.result || (!training && !after?.result)) return {found: false, reason: training ? 'training original required' : 'both original revisions required'}
  if (sides.some(s => !complete(s))) return {found: false, reason: 'reader refused, incomplete or ambiguous original evidence'}
  if (training) {
    const found = before.result.rules.some(r => r.laws.some(replayed))
    return {found, reason: found ? 'training flaw reproduced on original code' : 'training flaw not reproduced on original code'}
  }
  // Only stated laws count, never --security candidates. Replay must explicitly name the original
  // reproduction; an environment-model schedule alone does not meet this bar. Constructor contexts
  // are part of the identity: another overload's proof cannot clear a still-broken original.
  const broken = before.result.rules.flatMap(rule => rule.laws.filter(replayed).map(claim => ({rule, claim})))
  const fixedRules = after!.result!.rules
  const found = broken.some(({rule, claim}) => {
    const family = familyKey(rule, claim)
    const original = before.result!.rules.filter(r => r.entry === rule.entry)
    const fixed = fixedRules.filter(r => r.entry === rule.entry)
    // Every original initializer stays covered. Every fixed initializer (including a newly added
    // one) must check this exact policy; a partial repair or omitted law is not a fixed counterpart.
    return original.every(r => r.laws.some(l => familyKey(r, l) === family))
      && original.every(r => fixed.some(f => ruleKey(f) === ruleKey(r)))
      && fixed.every(r => r.laws.some(l => familyKey(r, l) === family && ['proven', 'unknown'].includes(l.verdict)))
  })
  return {found, reason: found ? 'stated law, original replay, fixed not refuted' : 'no stated law with original replay and checked fixed counterpart'}
}
