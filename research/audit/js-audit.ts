// The baseline: the same spec compiled to one plain JavaScript loop over every (user, project) pair, with the atoms
// inlined, so the comparison is with the fastest straightforward JS, not with the interpreter.
import {compileFunction} from '../../core/machine.ts'
import {type Org, membershipSlots} from './model.ts'
import {type AtomName, type Bool, type Num, atomNames, atoms} from './spec.ts'

function numJs(num: Num): string {
  switch (num.op) {
    case 'const': return String(num.value)
    case 'role': return 'role'
    case 'plan': return 'plan'
    case 'staff': return 'staff'
    case 'userDomain': return 'userDomain'
    case 'sharedDomain': return 'sharedDomain'
  }
}

function boolJs(expr: Bool): string {
  switch (expr.op) {
    case '>=': return `(${numJs(expr.a)} >= ${numJs(expr.b)})`
    case '===': return `(${numJs(expr.a)} === ${numJs(expr.b)})`
    case 'and': return `(${expr.xs.map(boolJs).join(' && ')})`
    case 'or': return `(${expr.xs.map(boolJs).join(' || ')})`
    case 'not': return `(!${boolJs(expr.x)})`
    case 'atom': throw new Error('atoms only')
  }
}

export type AuditCounts = {allowedA: Float64Array, allowedB: Float64Array, gained: Float64Array, lost: Float64Array}

// Per user: the projects policy A allows, policy B allows, and the ones B gains and loses against A.
export function compileJsAudit(): (org: Org, tableA: Uint8Array, tableB: Uint8Array, firstUser: number, userCount: number, counts: AuditCounts) => void {
  const atomLines = atomNames.map((name: AtomName, bit) => `      if (${boolJs(atoms[name].expr)}) index |= ${1 << bit};`).join('\n')
  const source = `
    const {memberTeam, memberRole, staff: staffOf, userDomain: domainOf, plan: planOf, teamOf, sharedDomain: sharedOf, projects} = org;
    for (let user = firstUser; user < firstUser + userCount; user++) {
      const base = user * ${membershipSlots};
      const t0 = memberTeam[base], t1 = memberTeam[base + 1], t2 = memberTeam[base + 2], t3 = memberTeam[base + 3];
      const r0 = memberRole[base], r1 = memberRole[base + 1], r2 = memberRole[base + 2], r3 = memberRole[base + 3];
      const staff = staffOf[user], userDomain = domainOf[user];
      let a = 0, b = 0, gained = 0, lost = 0;
      for (let project = 0; project < projects; project++) {
        const team = teamOf[project];
        const role = team === t0 ? r0 : team === t1 ? r1 : team === t2 ? r2 : team === t3 ? r3 : 0;
        const plan = planOf[team], sharedDomain = sharedOf[project];
        let index = 0;
${atomLines}
        const inA = tableA[index], inB = tableB[index];
        a += inA; b += inB; gained += inB & (inA ^ 1); lost += inA & (inB ^ 1);
      }
      counts.allowedA[user] = a; counts.allowedB[user] = b; counts.gained[user] = gained; counts.lost[user] = lost;
    }`
  return compileFunction<ReturnType<typeof compileJsAudit>>(['org', 'tableA', 'tableB', 'firstUser', 'userCount', 'counts'], source)
}

// The clever baseline, written by hand for this schema: only the pairs where a pair atom can hold are visited, i.e.
// the projects of the user's own teams and the projects shared with the user's domain. Every other pair has role 0 and
// no sharing, so its atoms depend only on the user (staff) and the project's plan, and a histogram of projects by plan
// counts them: background[plan] × table[those atoms], minus the visited projects' background, plus their real value.
export function sparseJsAudit(org: Org, tableA: Uint8Array, tableB: Uint8Array, firstUser: number, userCount: number, counts: AuditCounts) {
  const {projects, teams, domains, memberTeam, memberRole, staff, userDomain, plan, teamOf, sharedDomain} = org
  const bit = (name: AtomName) => 1 << atomNames.indexOf(name)
  const [admin, access, paid, enterprise, isStaff, shared] = (['UserIsProjectAdmin', 'UserHasProjectAccess', 'PlanIncludesPasswordProtection', 'PlanIsEnterprise', 'UserIsSupportStaff', 'ProjectSharedWithUserDomain'] as const).map(bit)
  const planBits = [0, paid!, paid! | enterprise!]
  const byTeam: number[][] = Array.from({length: teams}, () => [])
  const byDomain: number[][] = Array.from({length: domains + 1}, () => [])
  const histogram = [0, 0, 0]
  const seen = new Int32Array(projects)
  let stamp = 0
  for (let project = 0; project < projects; project++) {
    byTeam[teamOf[project]!]!.push(project)
    if (sharedDomain[project]! > 0) byDomain[sharedDomain[project]!]!.push(project)
    histogram[plan[teamOf[project]!]!]!++
  }
  for (let user = firstUser; user < firstUser + userCount; user++) {
    const userBits = staff[user] === 1 ? isStaff! : 0
    let a = 0, b = 0, gained = 0, lost = 0
    const add = (index: number, sign: number) => {
      const inA = tableA[index]!, inB = tableB[index]!
      a += sign * inA; b += sign * inB; gained += sign * (inB & (inA ^ 1)); lost += sign * (inA & (inB ^ 1))
    }
    for (let p = 0; p < 3; p++) add(userBits | planBits[p]!, histogram[p]!)
    stamp++
    const visit = (project: number) => {
      if (seen[project] === stamp) return
      seen[project] = stamp
      const team = teamOf[project]!
      let role = 0
      for (let slot = 0; slot < membershipSlots; slot++) if (memberTeam[user * membershipSlots + slot] === team) role = memberRole[user * membershipSlots + slot]!
      const base = userBits | planBits[plan[team]!]!
      const index = base | (role >= 2 ? admin! : 0) | (role >= 1 ? access! : 0) | (sharedDomain[project] === userDomain[user] ? shared! : 0)
      add(base, -1)
      add(index, 1)
    }
    for (let slot = 0; slot < membershipSlots; slot++) {
      const team = memberTeam[user * membershipSlots + slot]!
      if (team >= 0) for (const project of byTeam[team]!) visit(project)
    }
    for (const project of byDomain[userDomain[user]!]!) visit(project)
    counts.allowedA[user] = a; counts.allowedB[user] = b; counts.gained[user] = gained; counts.lost[user] = lost
  }
}
