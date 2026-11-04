import {createHash} from 'node:crypto'
import {strict as assert} from 'node:assert'
import {voteExperiment} from './vote.ts'
import {prepareLemma, recursiveExperiment} from './recursive.ts'
import {refuseCyclic} from '../../kernel/cyclic.ts'

console.log(JSON.stringify({evidenceMode: 'untimed correctness only; wall durations are not performance evidence'}))
const digest = (p: unknown) => createHash('sha256').update(JSON.stringify(p)).digest('hex')
const voteBaseline = voteExperiment(false), vote = voteExperiment(true), missingVote = voteExperiment(true, true)
assert(!voteBaseline.checked && vote.checked && !missingVote.checked)
const voteAblation = structuredClone(vote.proof!)
voteAblation.nodes[0]!.insts = []
const voteAblationRefusal = refuseCyclic(voteAblation)
assert(voteAblationRefusal)
console.log(JSON.stringify({milestone: 'synthetic vote-to-proposal', baseline: {checked: voteBaseline.checked, reason: voteBaseline.reason}, enabled: {checked: vote.checked, instances: vote.instances, matchingUnits: vote.matchingUnits, matchingMs: vote.matchingMs, proofUnits: vote.proofUnits, hintUnits: vote.hintUnits, proofMs: vote.ms, certificateSha256: digest(vote.proof)}, controls: {missingVote: missingVote.checked, voteAblationRefusal}}))
const prepared = prepareLemma(), v = prepared.verdict
console.log(JSON.stringify({milestone: 'real list reverse-append lemma preparation', checked: v.checked, proven: v.proven, ms: prepared.ms, proofUnits: prepared.proofUnits, goal: v.goal, stuck: v.stuck, node: v.node}))
assert(v.proven && v.checked && v.proof?.proven && v.node !== undefined)
const lemma = v.proof.proof
const baseline = recursiveExperiment(lemma, v.node, false), enabled = recursiveExperiment(lemma, v.node, true)
console.log(JSON.stringify({milestone: 'synthetic recursive-tail lemma use', baseline: {checked: baseline.checked, reason: baseline.reason}, enabled: {checked: enabled.checked, reason: enabled.reason, matches: enabled.matches, lemmaUses: enabled.lemmaUses, matchingUnits: enabled.matchingUnits, matchingMs: enabled.matchingMs, proofUnits: enabled.proofUnits, hintUnits: enabled.hintUnits, proofMs: enabled.ms, certificateSha256: enabled.proof && digest(enabled.proof)}, controls: {removedUse: enabled.removedUse, badRank: enabled.badRank}}))
assert(!baseline.checked && enabled.checked && enabled.lemmaUses > 0 && enabled.removedUse && enabled.badRank)
console.log(JSON.stringify({decision: 'GO for isolated synthetic experiment only', historicalQ3Measured: false, tipCorpusMeasured: false, mergeAuthorized: false}))
