// The fast path against the generic Datalog engine, on small orgs, with and without the stray grant.
import {evaluate} from './datalog.ts'
import {audit} from './fast.ts'
import {closure, derive, generate} from './model.ts'
for (const stray of [false, true]) for (const seed of [1, 2, 3]) {
  const org = generate(300, 120, stray, seed)
  const viewers = evaluate(org)
  const fast = audit(org)
  const {underFinance} = derive(org)
  let mismatches = 0, violations = 0
  for (let u = 0; u < org.users; u++) {
    let count = 0, bad = 0
    const member = (closure(org.userGroups[u]!, org.sub) & 1) !== 0
    for (let o = 0; o < org.objects; o++) if (viewers.has(`${u},${o}`)) { count++; if (underFinance[o] && !member) bad++ }
    if (count !== fast.viewable[u] || bad !== fast.violations[u]) mismatches++
    violations += bad
  }
  console.log(`seed ${seed}, stray ${stray}: ${viewers.size} viewer facts from Datalog; fast path ${mismatches === 0 ? 'agrees on every user' : `differs on ${mismatches} users`}; finance-law violations ${violations}`)
}
