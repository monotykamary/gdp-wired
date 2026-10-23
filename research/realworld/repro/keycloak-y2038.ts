// Repro for auth/keycloak/bruteForceProtector "past the failure factor, a failure disables the user at once".
// The prover's witness: a failure at failureTime = 2147483647000 ms (2038-01-19T03:14:07Z) with the failure factor
// reached. No JVM here, so the original can't be run; this reasons from the source, fetched at the pinned commit
// (keycloak 26.8.1, 24ed1dad), and replays the run on the rule's interpreter.
//
// DefaultBruteForceProtector.java (printed below):
//   :137  long notBefore = (failureTime / 1000) + waitSeconds;
//   :140  int notBeforeInt = notBefore > Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) notBefore;
//   :141  userLoginFailure.setFailedLoginNotBefore(notBeforeInt);
//   :275  long currTime = Time.currentTimeMillis() / 1000;
//   :277  if (currTime < failedLoginNotBefore) return true;   // temporarily disabled
// From 2038-01-19T03:14:07Z on, failureTime / 1000 >= Integer.MAX_VALUE, so notBefore is capped at Integer.MAX_VALUE
// and currTime < notBefore is false at once: the lockout that :129-143 just decided on never takes effect, and every
// later failure caps the same way, so from then on no temporary lockout ever disables anyone. The comment at :139 ("the
// user would be considered temporarily disabled with Integer.MAX_VALUE") assumes currTime < Integer.MAX_VALUE.
// (The column is an int too: UserLoginFailureAdapter.getFailedLoginNotBefore is Math.toIntExact of the entity's value.)
//   bun research/realworld/repro/keycloak-y2038.ts
import {bruteForce} from '../items/authz-keycloak.ts'

const base = 'https://raw.githubusercontent.com/keycloak/keycloak/24ed1dadf3f246a555adb6d3d4a99e9b3003fb3b'
const java = (await (await fetch(`${base}/services/src/main/java/org/keycloak/services/managers/DefaultBruteForceProtector.java`)).text()).split('\n')
for (const n of [137, 140, 141, 275, 276, 277]) console.log(`DefaultBruteForceProtector.java:${n}  ${java[n - 1]!.trim()}`)

// Java's arithmetic on the witness: one failure with failureFactor 1, waitIncrementSeconds 1, LINEAR strategy.
const INT_MAX = 2147483647n, failureTime = 2147483647000n
const wait = 1n * (1n + 1n - 1n), notBefore = failureTime / 1000n + wait
const notBeforeInt = notBefore > INT_MAX ? INT_MAX : notBefore, currTime = failureTime / 1000n
console.log(`\nfailureTime ${failureTime} ms: waitSeconds ${wait}, notBefore ${notBefore}, stored ${notBeforeInt}, currTime ${currTime}: isTemporarilyDisabled = ${currTime < notBeforeInt}`)

// The same request on the rule.
const r = bruteForce(), run = r.interpreter()
const params = r.encodeParams({perm: false, maxTemp: 0, multiple: false, inc: 1, factor: 1, maxDeltaSec: 43200, quickMs: 1000, minQuickSec: 60, maxWaitSec: 900, maxSec: 0} as never) // (its type lists the rule's .fns too)
let st = run.init(params)
for (const now of [Number(failureTime), Number(failureTime) + 5000]) {
  st = run.step(params, st, r.encodeInput({op: 'failure', cat: 'password', now}))
  const d = r.decode(st) as {nowSec: number, notBefore: number, fails: number}
  console.log(`rule: failure at ${now} ms -> fails ${d.fails}, notBefore ${d.notBefore}, now/1000 ${d.nowSec}: disabled = ${d.nowSec < d.notBefore}`)
}
