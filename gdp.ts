// The spec's predicates as gdp-ts trusted modules: the request path. Each prover stays private to this file, and each
// check runs the same expression that circuit.ts compiles, so a proof minted here and a bit of the audit agree.
import {type Named, type Proof, defineProof} from './vendor/gdp-ts/src/index.ts'
import {type Org, evalBool} from './model.ts'
import {type AtomName, atoms} from './spec.ts'

export type UserId = number & {readonly brand: 'UserId'}
export type ProjectId = number & {readonly brand: 'ProjectId'}

const provers = {
  UserIsProjectAdmin: defineProof('UserIsProjectAdmin'),
  UserHasProjectAccess: defineProof('UserHasProjectAccess'),
  PlanIncludesPasswordProtection: defineProof('PlanIncludesPasswordProtection'),
  PlanIsEnterprise: defineProof('PlanIsEnterprise'),
  UserIsSupportStaff: defineProof('UserIsSupportStaff'),
  ProjectSharedWithUserDomain: defineProof('ProjectSharedWithUserDomain'),
}

export interface UserIsProjectAdmin<U, P> extends Proof<'UserIsProjectAdmin', [U, P]> {}
export interface UserHasProjectAccess<U, P> extends Proof<'UserHasProjectAccess', [U, P]> {}
export interface PlanIncludesPasswordProtection<P> extends Proof<'PlanIncludesPasswordProtection', [P]> {}
export interface PlanIsEnterprise<P> extends Proof<'PlanIsEnterprise', [P]> {}
export interface UserIsSupportStaff<U> extends Proof<'UserIsSupportStaff', [U]> {}
export interface ProjectSharedWithUserDomain<U, P> extends Proof<'ProjectSharedWithUserDomain', [U, P]> {}

const holds = (org: Org, name: AtomName, user: number, project: number) => evalBool(org, atoms[name].expr, user, project)

export const userIsProjectAdmin = <U, P>(org: Org, user: Named<U, UserId>, project: Named<P, ProjectId>): UserIsProjectAdmin<U, P> | null =>
  holds(org, 'UserIsProjectAdmin', user.value, project.value) ? provers.UserIsProjectAdmin.prove(user, project) : null
export const userHasProjectAccess = <U, P>(org: Org, user: Named<U, UserId>, project: Named<P, ProjectId>): UserHasProjectAccess<U, P> | null =>
  holds(org, 'UserHasProjectAccess', user.value, project.value) ? provers.UserHasProjectAccess.prove(user, project) : null
export const planIncludesPasswordProtection = <P>(org: Org, project: Named<P, ProjectId>): PlanIncludesPasswordProtection<P> | null =>
  holds(org, 'PlanIncludesPasswordProtection', 0, project.value) ? provers.PlanIncludesPasswordProtection.prove(project) : null
export const planIsEnterprise = <P>(org: Org, project: Named<P, ProjectId>): PlanIsEnterprise<P> | null =>
  holds(org, 'PlanIsEnterprise', 0, project.value) ? provers.PlanIsEnterprise.prove(project) : null
export const userIsSupportStaff = <U>(org: Org, user: Named<U, UserId>): UserIsSupportStaff<U> | null =>
  holds(org, 'UserIsSupportStaff', user.value, 0) ? provers.UserIsSupportStaff.prove(user) : null
export const projectSharedWithUserDomain = <U, P>(org: Org, user: Named<U, UserId>, project: Named<P, ProjectId>): ProjectSharedWithUserDomain<U, P> | null =>
  holds(org, 'ProjectSharedWithUserDomain', user.value, project.value) ? provers.ProjectSharedWithUserDomain.prove(user, project) : null

// spec.ts's policies.canViewProtection as a union of proofs. The order only decides which proof is returned.
export type CanViewProtection<U, P> =
  | UserIsProjectAdmin<U, P>
  | UserHasProjectAccess<U, P>
  | {staff: UserIsSupportStaff<U>, enterprise: PlanIsEnterprise<P>}
  | ProjectSharedWithUserDomain<U, P>

export function canViewProtection<U, P>(org: Org, user: Named<U, UserId>, project: Named<P, ProjectId>): CanViewProtection<U, P> | null {
  const admin = userIsProjectAdmin(org, user, project)
  if (admin) return admin
  const access = userHasProjectAccess(org, user, project)
  if (access) return access
  const staff = userIsSupportStaff(org, user)
  const enterprise = planIsEnterprise(org, project)
  if (staff && enterprise) return {staff, enterprise}
  return projectSharedWithUserDomain(org, user, project)
}

// spec.ts's policies.canSetProtection: both proofs, as examples/basic's setPasswordProtection takes them.
export type CanSetProtection<U, P> = {manage: UserIsProjectAdmin<U, P>, plan: PlanIncludesPasswordProtection<P>}

export function canSetProtection<U, P>(org: Org, user: Named<U, UserId>, project: Named<P, ProjectId>): CanSetProtection<U, P> | null {
  const manage = userIsProjectAdmin(org, user, project)
  const plan = planIncludesPasswordProtection(org, project)
  return manage && plan ? {manage, plan} : null
}
