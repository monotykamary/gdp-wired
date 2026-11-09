import {readFileSync, writeFileSync} from 'node:fs'
const dir = process.argv[2]!, out = process.argv[3]!
const records = [1, 2, 3].map(repeat => {
  const text = readFileSync(`${dir}/original-pair-${repeat}.log`, 'utf8')
  return {repeat, records: ['BASELINE', 'CANDIDATE'].map((side, i) => {
    const section = text.split(`=== ${side} ===`)[1]!.split('=== ')[0]!, lines = section.split('\n')
    const raw = JSON.parse(lines.find(l => l.startsWith('{"id":"mldr"'))!).search
    const tries = (name: string) => lines.filter(l => l.startsWith('counts: try ') && l.includes(name))
    const safety = tries('one primary per term'), quorum = tries('no quorum canVote/3'), overlap = tries('stored guard reconfigs/inS or disabled/0'), fields = tries('fields: CV[a]=CV[b] and CfgT[a]=CfgT[b]')
    return {side: i ? 'candidate' : 'baseline', verdict: raw.verdict, why: raw.why, wallMs: raw.ms, work: raw.work, full: raw.full, finalLaws: raw.found?.length,
      safetyAttempts: safety.length, lastSafetyAttempts: safety.slice(-4), quorumAttempts: quorum.length, lastQuorumAttempts: quorum.slice(-4), overlapAttempts: overlap.length, lastOverlapAttempts: overlap.slice(-4), fieldAttempts: fields.length, lastFieldAttempts: fields.slice(-4), rounds: lines.filter(l => l.startsWith('counts: round ')).slice(-5), profile: lines.findLast(l => l.startsWith('counts: prof total '))}
  })}
})
writeFileSync(out, JSON.stringify(records, null, 2) + '\n')
console.log(JSON.stringify(records, null, 2))
