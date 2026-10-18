// Four ways to the same answers, compared exactly:
//   1. the interpreter (model.ts's evalBool) and the policy formulas, pair by pair
//   2. gdp.ts's provers: a proof is minted exactly where the policy holds
//   3. js-audit.ts: the spec compiled to one plain JavaScript loop
//   4. circuit.ts: the spec compiled to a Handwired loop program, run as generated JavaScript on the CPU
// Usage: bun check.ts [users] [projects] [teams] [domains]
import {name} from '../../vendor/gdp-ts/src/index.ts'
import {createLoopRunner, describeLoop} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {buildAudit, userCells, writeUserCells} from './circuit.ts'
import {type ProjectId, type UserId, canSetProtection, canViewProtection} from './gdp.ts'
import {compileJsAudit} from './js-audit.ts'
import {type Org, evalBool, generateOrg} from './model.ts'
import {type AtomName, atomNames, atoms, evalFormula, policies, truthTable} from './spec.ts'

const [users = 2000, projects = 512, teams = 200, domains = 50] = process.argv.slice(2).map(Number)
const org = generateOrg({users, teams, projects, domains})
const tableA = truthTable(policies.canViewProtection)
const tableB = truthTable(policies.canViewProtectionProposed)
let failures = 0
const fail = (message: string) => {
  if (failures++ < 10) console.log('MISMATCH', message)
}

const holds = (org: Org, user: number, project: number) => (atom: AtomName) => evalBool(org, atoms[atom].expr, user, project)

// 2 against 1, on every pair.
let minted = 0
for (let user = 0; user < users; user++) {
  for (let project = 0; project < projects; project++) {
    const atom = holds(org, user, project)
    name(user as UserId, project as ProjectId, (u, p) => {
      const view = canViewProtection(org, u, p)
      const set = canSetProtection(org, u, p)
      if ((view !== null) !== evalFormula(policies.canViewProtection, atom)) fail(`view proof, user ${user} project ${project}`)
      if ((set !== null) !== evalFormula(policies.canSetProtection, atom)) fail(`set proof, user ${user} project ${project}`)
      if (view) minted++
    })
  }
}

// 3 against 1.
const counts = () => ({allowedA: new Float64Array(users), allowedB: new Float64Array(users), gained: new Float64Array(users), lost: new Float64Array(users)})
const reference = counts()
for (let user = 0; user < users; user++) {
  for (let project = 0; project < projects; project++) {
    const atom = holds(org, user, project)
    const a = evalFormula(policies.canViewProtection, atom), b = evalFormula(policies.canViewProtectionProposed, atom)
    reference.allowedA[user]! += +a
    reference.allowedB[user]! += +b
    reference.gained[user]! += +(b && !a)
    reference.lost[user]! += +(a && !b)
  }
}
const jsAudit = compileJsAudit()
const js = counts()
jsAudit(org, tableA, tableB, 0, users, js)
for (const key of ['allowedA', 'allowedB', 'gained', 'lost'] as const) {
  for (let user = 0; user < users; user++) if (js[key][user] !== reference[key][user]) fail(`js ${key} user ${user}`)
}

// 4 against 1, counts for every user and the per-project codes for every user.
const built = buildAudit({projects, teams, domains})
const shared = new Float32Array(built.loop.sharedValues)
built.writeShared(shared, org, tableA, tableB)
const runner = createLoopRunner(built.loop, 'generated')
runner.setShared(shared)
const userBuffer = writeUserCells(org)
const outputs = [new Float32Array(users * 4), new Float32Array(projects)]
for (let user = 0; user < users; user++) {
  runner.run([userBuffer], user, outputs, user, 0)
  for (let project = 0; project < projects; project++) {
    const atom = holds(org, user, project)
    const expected = +evalFormula(policies.canViewProtection, atom) + 2 * +evalFormula(policies.canViewProtectionProposed, atom)
    if (outputs[1]![project] !== expected) fail(`circuit code user ${user} project ${project}: ${outputs[1]![project]} vs ${expected}`)
  }
}
const keys = ['allowedA', 'allowedB', 'gained', 'lost'] as const
for (let user = 0; user < users; user++) {
  keys.forEach((key, column) => {
    if (outputs[0]![user * 4 + column] !== reference[key][user]) fail(`circuit ${key} user ${user}`)
  })
}

const sum = (values: Float64Array) => values.reduce((total, value) => total + value, 0)
console.log(`${users} users × ${projects} projects = ${(users * projects).toLocaleString()} pairs, ${atomNames.length} atoms`)
console.log('step:', JSON.stringify(describeLoop(built.loop)), `user cells ${userCells}, shared cells ${shared.length}`)
console.log(`canView today ${sum(reference.allowedA)}, proposed ${sum(reference.allowedB)}, gained ${sum(reference.gained)}, lost ${sum(reference.lost)}, view proofs minted ${minted}`)
console.log(failures === 0 ? 'ALL AGREE: interpreter, gdp-ts provers, JS audit, Handwired circuit' : `${failures} MISMATCHES`)
process.exit(failures === 0 ? 0 : 1)
