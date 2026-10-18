// Laws over every sequence of requests, by the same enumeration: a law that holds at the start and that one step
// preserves holds after any sequence (induction, proven once for every law, as a hand-written Bend proof does by induction). What is
// left is the one-step check, a law about one decision, which enumeration decides when its arithmetic stays small.
// The models are the caps rule (per-key caps) and the budget rule's step (bounded loss).
// Usage: bun steps.ts

// --- caps, from caps rule --------------------------------------------------------------------------------------
// For one key kind (account, day, hour, domain) and any one key x of it: the count of grants with key x stays within
// the cap. One step: a request with key k is granted when ok and every key kind is under its cap, and then the count of
// k grows by 1. The other three kinds' "under" bits are left free, so the check holds whatever they are.
// The check compares counts with caps and adds 1, which is difference logic (x − y ≤ c): if a counterexample exists,
// one exists with every value within 0..(variables × largest offset), here 0..4. Enumerating 0..8 decides it.
function capStepHolds(count: number, cap: number, sameKey: boolean, ok: boolean, othersUnder: boolean): boolean {
  if (count > cap) return true // only states where the law holds are stepped
  const under = count < cap // the caps rule's `under`: lt(count(k, key(k, r), h), cap(k, ...)), at k = x when sameKey
  const granted = ok && othersUnder && (sameKey ? under : true)
  const next = count + (granted && sameKey ? 1 : 0)
  return next <= cap
}
let capCases = 0, capFailures = 0
for (let count = 0; count <= 8; count++) for (let cap = 0; cap <= 8; cap++)
  for (const sameKey of [false, true]) for (const ok of [false, true]) for (const othersUnder of [false, true]) {
    capCases++
    if (!capStepHolds(count, cap, sameKey, ok, othersUnder)) capFailures++
  }
console.log(`caps (caps_hold, day_cap, hour_cap, domain_cap; once_per_account is cap 1): start 0 <= cap, and one step ${capFailures === 0 ? 'PRESERVES' : 'BREAKS'} count <= cap in all ${capCases} cases of the small model`)

// A law that isn't inductive on its own fails the step check with a state the system never reaches. E.g. "count <= cap"
// stepped without the guard `under` (a policy that forgot the cap):
let forgot = 0
for (let count = 0; count <= 8; count++) for (let cap = 0; cap <= 8; cap++) if (count <= cap && !(count + 1 <= cap)) forgot++
console.log(`  a step that forgets the guard: ${forgot} counterexamples, e.g. count 0, cap 0, a granted request with key x`)

// --- bounded loss, from budget rule ----------------------------------------------------------------------------
// step(s, b, c, m) = s + min(c, m) if s < b, else s. Law: s <= b + m, from s = 0.
// The step check adds three quantities (s + min(c, m) <= b + m), which is linear arithmetic, not difference logic. Its
// small-model bound (Papadimitriou 1981: n(ma)^(2m+1) for n variables and m constraints) is about 10^13 per variable
// here, too many to enumerate, so a box of values is evidence, not a decision.
const step = (s: number, b: number, c: number, m: number) => (s < b ? s + Math.min(c, m) : s)
const box = 96
let lossCases = 0, lossFailures = 0
for (let s = 0; s <= box; s++) for (let b = 0; b <= box; b++) for (let c = 0; c <= box; c++) for (let m = 0; m <= box; m++) {
  if (s > b + m) continue
  lossCases++
  if (step(s, b, c, m) > b + m) lossFailures++
}
console.log(`bounded loss: one step keeps s <= b + m in ${lossCases.toLocaleString()} cases of 0..${box} (${lossFailures} failures), evidence only`)

// The same law after a change of variables that leaves only differences: h = b − s, the budget left (negative after an
// overshoot), and t = min(c, m), the request's capped cost, with 0 <= t <= m. Then step: h' = h − t when h > 0, and the
// law is h >= −m. That's still t and m against h', three quantities, so the change of variables doesn't help: the
// arithmetic itself is the obstacle, and a solver for linear integer arithmetic (an SMT solver) decides it instead.
