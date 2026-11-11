// Internal proposal capability, not a proof receipt or acceptance token.
// Public/standalone strategy entry points never supply it. Only the full-work
// counted dispatcher may defer STEP to its unchanged final family checker.
import {completeWorkProfile} from './work-profile.ts'
import {env} from './solver.ts'
export const familyStepProposal: unique symbol = Symbol('unchecked family STEP proposal')
export type FamilyStepProposal = typeof familyStepProposal
export const finalCountStepDeferralEnabled = (): boolean => completeWorkProfile.enabled && env.GDP_COUNT_FINAL_DEFER_CHECKS === '1'
export const deferFinalCountStep = (key?: FamilyStepProposal): boolean => key === familyStepProposal && finalCountStepDeferralEnabled()
// No cache: every invocation calls the original checker on the current objects.
// The opt-in path turns malformed/throwing/expired checks into clean refusal.
export function closingCountCheck(check: () => boolean): boolean {
  if (!finalCountStepDeferralEnabled()) return check()
  try { return check() } catch { return false }
}
