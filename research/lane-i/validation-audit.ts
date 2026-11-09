// Iteration evidence only. This never replaces Lane D's final gate.
import {readFileSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
type Result = {id: string, search: {verdict: string, ms: number, [key: string]: unknown}}
type Timing = {event: string, at: number, searchMs?: number, attemptWallMs?: number}
export function parseMldrPair(log: string, repeat: number) {
  const issues: string[] = []
  const sides = ['base', 'candidate'].map(side => {
    const begin = `LANE_I_BEGIN mldr ${repeat} mldr ${side}`, end = `LANE_I_END mldr ${repeat} mldr ${side}`
    const lines = log.split('\n'), starts = lines.flatMap((line, i) => line === begin ? [i] : []), ends = lines.flatMap((line, i) => line === end ? [i] : [])
    if (starts.length !== 1 || ends.length !== 1 || ends[0]! <= starts[0]!) {
      issues.push(`${side}: phase cardinality/order`)
      return {side}
    }
    const text = lines.slice(starts[0]! + 1, ends[0]).join('\n')
    const results: Result[] = [], timing: Timing[] = []
    for (const line of text.split('\n')) {
      try {
        if (line.startsWith('{')) { const r = JSON.parse(line); if (r.id === 'mldr') results.push(r) }
        if (line.startsWith('LANE_I_TIMING ')) timing.push(JSON.parse(line.slice(14)))
      } catch { issues.push(`${side}: malformed JSON receipt`) }
    }
    const exits = [...text.matchAll(/^LANE_I_EXIT (\S+) (\d+)$/gm)]
    if (exits.length !== 1 || exits[0]![1] !== side || !['0', '124', '137'].includes(exits[0]![2]!)) issues.push(`${side}: invalid process exit`)
    if (results.length !== 1) issues.push(`${side}: expected one semantic result`)
    const result = results.length === 1 ? results[0] : undefined
    if (result && (!['proven', 'unknown', 'refuted'].includes(result.search?.verdict) || !Number.isFinite(result.search?.ms) || result.search.ms < 0 || result.search.ms > 60000)) issues.push(`${side}: invalid strict result`)
    const finish = timing.filter(t => t.event === 'result'), first = timing.filter(t => t.event === 'first-attempt-return'), generated = timing.filter(t => t.event === 'candidates')
    if (finish.length !== 1 || finish[0]?.searchMs !== result?.search?.ms) issues.push(`${side}: missing/mismatched result timing`)
    const start = finish.length === 1 && Number.isFinite(finish[0]!.searchMs) ? finish[0]!.at - finish[0]!.searchMs! : undefined
    const preAttemptWallMs = start !== undefined && first.length === 1 && Number.isFinite(first[0]!.attemptWallMs) ? first[0]!.at - first[0]!.attemptWallMs! - start : undefined
    const generationWallMs = start !== undefined && generated.length === 1 ? generated[0]!.at - start : undefined
    const attempts = [...text.matchAll(/counts: try (.*?) \| ls (\d+) pass ([01]) ms (\d+) took (\d+) wall (\d+) \[(.*?)\] -> (.*)/g)].map(m => ({law: m[1]!, family: Number(m[2]), pass: Number(m[3]), allowance: Number(m[4]), units: Number(m[5]), wallMs: Number(m[6]), outcome: m[8]!}))
    const candidates = [...text.matchAll(/counts: candidates at \d+ ms: (.*)/g)].map(m => m[1]!.split('; '))
    return {side, result, exit: exits[0]?.[2], preAttemptWallMs, generationWallMs, candidates, attempts, kept: attempts.filter(a => a.outcome === 'kept'), safetyTried: attempts.some(a => a.law === 'one primary per term')}
  })
  return {repeat, issues, sides}
}
export function parseReplayNegative(log: string) {
  const markers = log.match(/^CORE_REPLAY_NEGATIVE_CONTROL_OK$/gm) ?? []
  const expected = /^\s*0 pass\s*$/m.test(log) && /^\s*1 fail\s*$/m.test(log) && /\(fail\) ordinary core replay retains metadata/.test(log) && /"readsRetained":\s*false/.test(log) && /"certificatesRetained":\s*true/.test(log) && /"poolsRetained":\s*true/.test(log) && !/^\s*[1-9]\d* errors?\s*$/m.test(log)
  const issues = markers.length === 1 && expected ? [] : ['missing or invalid replay negative control']
  return {issues, expectedRejection: issues.length === 0}
}
export function parseTestSummary(log: string) {
  const passes = [...log.matchAll(/^\s*(\d+) pass\s*$/gm)], failures = [...log.matchAll(/^\s*(\d+) fail\s*$/gm)], assertions = [...log.matchAll(/^\s*(\d+) expect\(\) calls\s*$/gm)]
  const issues: string[] = []
  if (passes.length !== 1 || Number(passes[0]?.[1]) <= 0 || failures.length !== 1 || Number(failures[0]?.[1]) !== 0 || /^\s*[1-9]\d* errors?\s*$/m.test(log)) issues.push('invalid or failing test summary')
  return {issues, passed: Number(passes[0]?.[1] ?? 0), assertions: Number(assertions[0]?.[1] ?? 0)}
}
if (import.meta.main) {
  const root = process.argv[2]; if (!root) throw Error('iteration root required')
  const dir = join(root, 'validation'), identity = JSON.parse(readFileSync(join(root, 'input/identity.json'), 'utf8')), placement = JSON.parse(readFileSync(join(dir, 'placement.json'), 'utf8'))
  const rows = readFileSync(join(dir, 'summary.tsv'), 'utf8').trim().split('\n').map(line => line.split('\t')), names = ['check', ...[1, 2, 3, 4].map(i => `changed-tests-${i}`), ...[1, 2, 3].map(i => `mldr-r${i}`), ...(process.argv[3] === '--replay-negative' ? ['core-replay-negative'] : [])], issues: string[] = []
  if (rows.length !== names.length || new Set(rows.map(row => row[0])).size !== names.length || rows.some(row => !names.includes(row[0]!))) issues.push('validation roster mismatch')
  const jobs = names.map(name => {
    const row = rows.find(r => r[0] === name), p = placement[name], log = readFileSync(join(dir, name + '.log'), 'utf8')
    if (row?.[1] !== '0' || row?.[3] !== 'boat' || !p?.exclusive || p.co_tenants !== 0 || p.type !== 'large' || !p.cpu) issues.push(`${name}: exit/backend/CPU placement`)
    if (name.startsWith('mldr-') && (!log.includes(identity.candidate) || !log.includes(identity.baseline))) issues.push(`${name}: source identity missing`)
    const parsed = name.startsWith('mldr-') ? parseMldrPair(log, Number(name.slice(-1))) : name.startsWith('changed-tests-') ? parseTestSummary(log) : name === 'core-replay-negative' ? parseReplayNegative(log) : {issues: []}
    issues.push(...parsed.issues.map(issue => `${name}: ${issue}`))
    return {name, placement: p, sha256: createHash('sha256').update(log).digest('hex'), ...parsed}
  })
  const report = {finalGate: false, identity, issues, jobs}
  writeFileSync(join(root, 'validation-audit.json'), JSON.stringify(report, null, 2) + '\n')
  console.log(JSON.stringify(report, null, 2))
  if (issues.length) process.exitCode = 1
}
