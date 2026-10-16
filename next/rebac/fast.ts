// The fast JS path: per user, the group closure, then each object by the derived tables.
import {type Org, closure, derive} from './model.ts'

export type Audit = {viewable: Uint32Array, violations: Uint32Array}
export function audit(org: Org, derived = derive(org)): Audit {
  const {inherited, tin, tout, underFinance} = derived
  const viewable = new Uint32Array(org.users), violations = new Uint32Array(org.users)
  const financeMask = 1 << org.financeGroup
  for (let u = 0; u < org.users; u++) {
    const groups = closure(org.userGroups[u]!, org.sub)
    const d0 = org.userGrant[2 * u]!, d1 = org.userGrant[2 * u + 1]!
    const lo0 = d0 >= 0 ? tin[d0]! : 1, hi0 = d0 >= 0 ? tout[d0]! : 0, lo1 = d1 >= 0 ? tin[d1]! : 1, hi1 = d1 >= 0 ? tout[d1]! : 0
    const member = (groups & financeMask) !== 0
    let count = 0, bad = 0
    for (let o = 0; o < org.objects; o++) {
      const t = tin[o]!
      const sees = (inherited[o]! & groups) !== 0 || (t >= lo0 && t <= hi0) || (t >= lo1 && t <= hi1)
      if (sees) {
        count++
        if (underFinance[o] && !member) bad++
      }
    }
    viewable[u] = count
    violations[u] = bad
  }
  return {viewable, violations}
}
