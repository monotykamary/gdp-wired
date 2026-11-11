// An opt-in research profile, not a calibration. D2 owns the eventual weights
// and W. Freeze the flag once: changing process.env during a proof must not
// remove already-counted work or change its unit definition.
import {coreMeter} from './meter.ts'
import {completeWorkProfile} from './work-profile.ts'
const environment = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env
export const stepWorkProfile = Object.freeze({id: 'core-steps-v0', enabled: environment?.GDP_WORK_STEPS === '1' || completeWorkProfile.enabled, provisional: true as const})
export const provisionalStepWeights = Object.freeze({astNodes: 1, evals: 1, cubeTests: 1, ticks: 1})
export function stepWork(): number {
  if (!stepWorkProfile.enabled || completeWorkProfile.enabled) return 0
  return coreMeter.astNodes * provisionalStepWeights.astNodes + coreMeter.evals * provisionalStepWeights.evals
    + coreMeter.cubeTests * provisionalStepWeights.cubeTests + coreMeter.ticks * provisionalStepWeights.ticks
}
