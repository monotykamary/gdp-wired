// gdp-ts's example, its checks proven: who may change a project's password protection (gdp-ts's README) as a guard,
// and sign-in under a lockout as a gate. The sensitive functions demand gdp-ts proofs; the trusted modules mint them
// only through gdp-wired, which proved each check's laws when the module loaded.
//   bun examples/gdp.ts
import {type Named, type Proof, defineProof, name} from '@gdp-ts/core'
import {fun, nat, no, oneOf, rule, when} from '../core/dsl.ts'
import {Unproven, gate, guard} from '../core/gdp.ts'

type ProjectId = string
type UserId = string

// --- proofs/can-set-protection.ts: a trusted module ------------------------------------------------------------------
// Owners and members may change password protection, and only on a plan that includes it.
const canSet = fun('can set password protection')
  .inputs({role: oneOf('owner', 'member', 'viewer', 'none'), plan: oneOf('free', 'pro', 'enterprise')})
  .returns(({role, plan}) => ({allow: role.is('owner').or(role.is('member')).and(plan.is('free').not())}))
const canSetLaws = [
  canSet.law('a viewer never changes protection', ({role}, out) => [role.is('viewer'), out.allow], () => no),
  canSet.law('nobody outside the team changes protection', ({role}, out) => [role.is('none'), out.allow], () => no),
  canSet.law('the free plan never has protection', ({plan}, out) => [plan.is('free'), out.allow], () => no),
  canSet.law('an owner on enterprise always can', ({role, plan}) => [role.is('owner'), plan.is('enterprise')], out => out.allow),
]
const CanSetProtection = defineProof('CanSetProtection') // not exported
export interface CanSetProtection<U, P> extends Proof<'CanSetProtection', [U, P]> {}
const mintCanSet = guard(CanSetProtection, canSet, 'allow', {laws: canSetLaws})
const db = {
  role: (u: UserId, p: ProjectId) => (p === 'p1' && u === 'ada' ? 'owner' : p === 'p1' && u === 'bo' ? 'viewer' : 'none'),
  plan: (p: ProjectId) => (p === 'p1' ? 'enterprise' : 'free'),
}
export const canSetProtection = <U, P>(user: Named<U, UserId>, project: Named<P, ProjectId>): CanSetProtection<U, P> | null =>
  mintCanSet({role: db.role(user.value, project.value), plan: db.plan(project.value)}, user, project)

// --- proofs/signed-in.ts: a trusted module with state -----------------------------------------------------------------
// Each failed sign-in while unlocked counts; the one that reaches maxFails locks the account; a success while unlocked
// clears the count and signs in; only an administrator's unlock clears a lock.
const lockout = rule('sign-in lockout')
  .params({maxFails: nat})
  .pre(({maxFails}) => maxFails.atLeast(1))
  .inputs({kind: oneOf('fail', 'success', 'unlock')})
  .state({fails: 0, locked: 0})
  .flags(({kind, locked}) => ({signedIn: kind.is('success').and(locked.eq(0))}))
  .step(({kind, maxFails, fails, locked, signedIn}) => ({
    fails: when(kind.is('fail').and(locked.eq(0)), fails.plus(1), when(signedIn.or(kind.is('unlock')), 0, fails)),
    locked: when(kind.is('fail').and(locked.eq(0), fails.plus(1).atLeast(maxFails)), 1, when(kind.is('unlock'), 0, locked)),
  }))
const lockoutLaws = [
  lockout.law('an unlocked account is below maxFails', ({locked, fails, maxFails}) => locked.eq(0).implies(fails.lt(maxFails))),
  lockout.law('locked is a yes or no', ({locked}) => locked.atMost(1)),
]
const signedInWhileUnlocked = lockout.stepLaw('a sign-in happens only while unlocked', ({locked}) => locked.eq(0), ({signedIn}) => signedIn)
const SignedIn = defineProof('SignedIn') // not exported
export interface SignedIn<U> extends Proof<'SignedIn', [U]> {}
// One gate per account (here, one account); a server keeps each account's state and passes it back as `state`.
const account = gate(SignedIn, lockout, 'signedIn', {laws: lockoutLaws, stepLaws: [signedInWhileUnlocked], params: {maxFails: 3}})
export const signIn = <U>(user: Named<U, UserId>, passwordOk: boolean): SignedIn<U> | null =>
  account.request({kind: passwordOk ? 'success' : 'fail'}, user)

// --- data/projects.ts: sensitive, demands the proofs -------------------------------------------------------------------
const protectedProjects = new Set<ProjectId>()
function setPasswordProtection<U, P>(project: Named<P, ProjectId>, _proofs: {signedIn: SignedIn<U>, canSet: CanSetProtection<U, P>}): void {
  protectedProjects.add(project.value)
}

// --- the route --------------------------------------------------------------------------------------------------------
const attempt = (userId: UserId, passwordOk: boolean, projectId: ProjectId): string =>
  name(userId, projectId, (user, project) => {
    const signedIn = signIn(user, passwordOk)
    if (!signedIn) return 'not signed in'
    const canSet = canSetProtection(user, project)
    if (!canSet) return 'forbidden'
    setPasswordProtection(project, {signedIn, canSet})
    return 'protected'
  })

const seen = [
  attempt('bo', true, 'p1'), // a viewer
  attempt('ada', false, 'p1'), attempt('ada', false, 'p1'), attempt('ada', false, 'p1'), // three failures lock it
  attempt('ada', true, 'p1'), // locked: the right password signs nobody in
]
account.request({kind: 'unlock'})
seen.push(attempt('ada', true, 'p1'))
console.log(seen.join(', '))
if (seen.join() !== 'forbidden,not signed in,not signed in,not signed in,not signed in,protected') throw new Error('unexpected outcomes')

// A check whose law fails never becomes a trusted module: members on the free plan, say.
const loose = canSet.returns(({role}) => ({allow: role.is('owner').or(role.is('member'))}))
try {
  guard(defineProof('CanSetProtection'), loose, 'allow', {laws: [loose.law('the free plan never has protection', ({plan}, out) => [plan.is('free'), out.allow], () => no)]})
  throw new Error('a loose check was accepted')
} catch (e) {
  if (!(e instanceof Unproven)) throw e
  console.log(`refused: ${e.message}`)
}
