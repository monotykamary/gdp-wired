// Untrusted local-first scheduling. Only the caller's checked transporter can
// authorize a local result; local models/unknowns never replace the full query.
import {type Law} from './machine.ts'
import {clock, withDeadline} from '../kernel/prove.ts'
import {isLocalCountExpiration} from './count-tier-budget.ts'
import {type CountPremiseContext} from './count-premise-view.ts'
import {withTableAdmission} from './table-admission.ts'

export function countPremiseSearch<T>(family: Law[], until: number,
  contexts: (until: number) => CountPremiseContext[],
  probe: (family: Law[], until: number) => T,
  accept: (context: CountPremiseContext, result: T, until: number) => T | undefined,
  observe?: (event: {phase: 'premise-context', outcome: 'proved' | 'declined' | 'expired' | 'fallback', local: number, whole: number, guardReads?: boolean}) => void,
  decline: (error: unknown) => boolean = () => false,
): T {
  // Selection, both local searches and their transport share this allowance.
  // The final quarter is never granted to a local search or its checker.
  const localEnd = clock() + Math.max(0, until - clock()) * 3 / 4
  const seen = new Set<string>()
  try {
    for (const context of withDeadline(localEnd, () => contexts(localEnd))) {
      if (clock() >= localEnd) break
      if (!context.laws.length || context.laws.length >= family.length || context.selected.length !== context.laws.length || context.laws.some((law, i) => family[context.selected[i]!] !== law)) continue
      const key = context.selected.join(',')
      if (seen.has(key)) continue
      seen.add(key)
      try {
        const result = withDeadline(localEnd, () => {
          const proposed = withTableAdmission(() => probe(context.laws, localEnd))
          return clock() < localEnd ? accept(context, proposed, localEnd) : undefined
        })
        observe?.({phase: 'premise-context', outcome: result !== undefined ? 'proved' : 'declined', local: context.laws.length, whole: family.length, guardReads: context.guardReads})
        if (result !== undefined) return result
      } catch (error) {
        if (!isLocalCountExpiration(error, until) && !decline(error)) throw error
        observe?.({phase: 'premise-context', outcome: decline(error) ? 'declined' : 'expired', local: context.laws.length, whole: family.length, guardReads: context.guardReads})
      }
    }
  } catch (error) {
    if (!isLocalCountExpiration(error, until) && !decline(error)) throw error
  }
  observe?.({phase: 'premise-context', outcome: 'fallback', local: family.length, whole: family.length})
  return withTableAdmission(() => probe(family, until))
}
