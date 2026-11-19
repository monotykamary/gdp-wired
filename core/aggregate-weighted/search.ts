import {type Law, type Machine, n, x} from '../machine.ts'
import {searchWall} from '../wall.ts'
import {type Instances, type Tree, obligations, sumParts} from '../../kernel/kernel.ts'
import {clock, grow, pastWall, withWall} from '../../kernel/prove.ts'
import {growCdcl} from '../../kernel/cdcl.ts'
import {type WeightedCandidate, type WeightedRecipe, weightedCandidates} from './candidates.ts'

export type WeightedProof = {instances: Record<string, Instances>, trees: Record<string, Tree>}
export type WeightedProposal = {
  kind: 'weighted', recipe: WeightedRecipe, machine: Machine, laws: Law[], pointLaw: string, proof: WeightedProof,
}
export type WeightedObserver = (event: Record<string, unknown>) => void

// Every seed is an ordinary instance of a premise of the original obligation.
// The output is a proposal only, even after its instrumented family checks.
function proveSeeded(candidate: WeightedCandidate, until: number, observe: WeightedObserver): WeightedProof | undefined {
  const {machine, laws, recipe: {point}, pointLaw, agreementLaw, sum} = candidate
  const law = laws.find(l => l.name === pointLaw)
  if (!law?.forall) return
  const probe = x(`${law.forall}#`)
  const touched = [point, ...(point.op === 'if' ? [point.then, point.else] : [])]
  const sumFlag = `?${sumParts(sum).flag}`
  const closedInstances = Object.fromEntries(Object.entries(machine.step.flags ?? {})
    .flatMap(([name, condition]) => condition.op === 'all' ? [[`?${name}`, [n(0)]]] : []))
  const instances: Record<string, Instances> = Object.fromEntries(laws.map(l => [l.name, {
    ...closedInstances,
    [pointLaw]: l === law ? [...touched, probe] : [point],
    [sumFlag]: l === law ? [probe] : [],
  }]))
  const trees: Record<string, Tree> = Object.create(null)
  const goals = obligations(machine, laws, instances)
  // Give the agreement obligation first refusal before the pointwise invariant.
  const agreement = 2 * laws.findIndex(l => l.name === agreementLaw)
  goals.unshift(...goals.splice(agreement, 2))
  for (const goal of goals) {
    if (clock() >= until || pastWall()) return
    const step = goal.name.endsWith(' @step')
    const end = Math.min(until, clock() + (step ? 30_000 : 2_000))
    const quick = grow(goal, new Map(), {nodes: 0, until: Math.min(end, clock() + (step ? 750 : 2_000))})
    const found = step && !('tree' in quick) && clock() < end && !pastWall()
      ? growCdcl(goal, new Map(), {nodes: 0, until: Math.min(end, clock() + 28_000)}) : quick
    observe({phase: 'goal', goal: goal.name, closed: 'tree' in found, remaining: Math.round(until - clock()),
      ...('tree' in found ? {} : {stuck: found.stuck, why: found.why})})
    if (!('tree' in found)) return
    trees[goal.name] = found.tree
  }
  // checkGhostWrite reconstructs this family from the source and checks it
  // before production can accept it. Avoid doing the same full check twice.
  return clock() < until && !pastWall() ? {instances, trees} : undefined
}

export function weightedSearch(source: Machine, law: Law, ms: number, observe: WeightedObserver = () => {}): WeightedProposal | undefined {
  if (!Number.isFinite(ms) || ms < 1000) return
  const capped = Math.min(ms, 60_000), until = clock() + capped
  return withWall(searchWall(capped), () => {
    try {
      for (const candidate of weightedCandidates(source, law)) {
        if (clock() >= until || pastWall()) break
        observe({phase: 'candidate', recipe: candidate.recipe})
        const proof = proveSeeded(candidate, until, observe)
        if (proof) return {kind: 'weighted', recipe: candidate.recipe, machine: candidate.machine,
          laws: candidate.laws, pointLaw: candidate.pointLaw, proof}
      }
    } catch (error) {
      observe({phase: 'error', error: String(error)})
    }
    return undefined
  })
}
