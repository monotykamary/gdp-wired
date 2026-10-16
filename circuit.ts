// The spec's predicates compiled into a Handwired loop program, in json-search's form: a document is one user, a
// position is one project, and the step decides every predicate for that (user, project) pair. Two policies are
// tables of 64 cells (spec.ts's truthTable), so a new policy writes cells and changes no shader.
//
// What one step computes, at project `position`:
//   team = teamOf[position], plan = planOf[team], sharedDomain = sharedOf[position]   three table reads
//   role = Σ memberRole[k] × [memberTeam[k] === team]                                  4 equality bits and 4 products
//   each atom: one comparison bit, from spec.ts's expression
//   A = policyA[Σ atom_i × 2^i], B = policyB[...]                                      two table reads
// and carries five registers: the position, and per user how many projects A allows, B allows, B gains and B loses.
import {type Circuit, type Wire, emitCompare} from './vendor/handwired/src/runtime/numeric-ui-core.ts'
import {createSourceTable, input, list} from './vendor/handwired/src/runtime/cells.ts'
import {type Binding, type LoopProgram, createStage} from './vendor/handwired/src/json-search/loop-program.ts'
import {type Bit, bitWire, noneOf, not} from './vendor/handwired/src/json-search/regex/bits.ts'
import {type Org, membershipSlots} from './model.ts'
import {type Bool, type Num, atomNames, atoms} from './spec.ts'

export const userCells = 2 * membershipSlots + 2
const registerNames = ['position', 'allowedA', 'allowedB', 'gained', 'lost'] as const

export function buildAudit(sizes: {projects: number, teams: number, domains: number}) {
  const {projects, teams, domains} = sizes
  const policyCells = 1 << atomNames.length
  const integer = (minimum: number, maximum: number) => input([minimum, maximum], {grid: 1, initial: minimum})
  const table = createSourceTable()
  const cells = table.declare({
    memberTeam: list(membershipSlots, () => integer(-1, teams - 1)),
    memberRole: list(membershipSlots, () => integer(0, 3)),
    staff: integer(0, 1),
    userDomain: integer(1, domains),
    position: integer(0, projects),
    allowedA: integer(0, projects),
    allowedB: integer(0, projects),
    gained: integer(0, projects),
    lost: integer(0, projects),
    tables: {
      teamOf: list(projects, () => integer(0, teams - 1)),
      sharedOf: list(projects, () => integer(0, domains)),
      planOf: list(teams, () => integer(0, 2)),
      policyA: list(policyCells, () => integer(0, 1)),
      policyB: list(policyCells, () => integer(0, 1)),
    },
  })
  const circuit: Circuit = table.createCircuit()
  const {tables} = cells
  const onGrid = (wire: Wire) => {
    circuit.assumeGrid(wire, 1)
    return wire
  }

  const team = onGrid(circuit.indexRead(cells.position, tables.teamOf))
  const plan = onGrid(circuit.indexRead(team, tables.planOf))
  const sharedDomain = onGrid(circuit.indexRead(cells.position, tables.sharedOf))
  const role = circuit.roundAffine(cells.memberTeam.map((memberTeam, slot) => {
    const here = emitCompare(circuit, memberTeam, '===', team)
    return [circuit.reglu([[cells.memberRole[slot]!, 1]], 0, [[here, 1]], 0), 1] as const
  }))
  circuit.assumeRange(role, 0, 3)
  onGrid(role)

  function num(expr: Num): Wire {
    switch (expr.op) {
      case 'const': return circuit.constant(expr.value)
      case 'role': return role
      case 'plan': return plan
      case 'staff': return cells.staff
      case 'userDomain': return cells.userDomain
      case 'sharedDomain': return sharedDomain
    }
  }
  function bool(expr: Bool): Bit {
    switch (expr.op) {
      case '>=': return emitCompare(circuit, num(expr.a), '>=', num(expr.b))
      case '===': return emitCompare(circuit, num(expr.a), '===', num(expr.b))
      case 'not': return not(circuit, bool(expr.x))
      case 'or': return not(circuit, noneOf(circuit, expr.xs.map(bool)))
      case 'and': {
        const bits = expr.xs.map(bool)
        if (bits.includes(false)) return false
        const wires = bits.filter((bit): bit is Wire => typeof bit !== 'boolean')
        if (wires.length === 0) return true
        if (wires.length === 1) return wires[0]!
        // JS: every bit is 1, as relu(sum − (n − 1)).
        return circuit.reglu([], 1, wires.map(wire => [wire, 1] as const), 1 - wires.length)
      }
      case 'atom': throw new Error('a predicate reads facts, not other predicates')
    }
  }

  const atomBits = atomNames.map(name => bitWire(circuit, bool(atoms[name].expr)))
  const policyIndex = onGrid(circuit.roundAffine(atomBits.map((bit, index) => [bit, 2 ** index] as const)))
  circuit.assumeRange(policyIndex, 0, policyCells - 1)
  const inA = onGrid(circuit.indexRead(policyIndex, tables.policyA))
  const inB = onGrid(circuit.indexRead(policyIndex, tables.policyB))
  const next = {
    position: circuit.roundAffine([[cells.position, 1]], 1),
    allowedA: circuit.roundAffine([[cells.allowedA, 1], [inA, 1]]),
    allowedB: circuit.roundAffine([[cells.allowedB, 1], [inB, 1]]),
    gained: circuit.roundAffine([[cells.gained, 1], [circuit.reglu([], 1, [[inB, 1], [inA, -1]], 0), 1]]),
    lost: circuit.roundAffine([[cells.lost, 1], [circuit.reglu([], 1, [[inA, 1], [inB, -1]], 0), 1]]),
  }
  // Per position, for the users of a window: 0 neither, 1 only A, 2 only B, 3 both.
  const code = circuit.roundAffine([[inA, 1], [inB, 2]])

  const {initialSource} = table.finish()
  const bindings = new Map<Wire, Binding>([
    ...cells.memberTeam.map((wire, slot): [Wire, Binding] => [wire, {kind: 'cell', buffer: 0, column: slot}]),
    ...cells.memberRole.map((wire, slot): [Wire, Binding] => [wire, {kind: 'cell', buffer: 0, column: membershipSlots + slot}]),
    [cells.staff, {kind: 'cell', buffer: 0, column: 2 * membershipSlots}],
    [cells.userDomain, {kind: 'cell', buffer: 0, column: 2 * membershipSlots + 1}],
    ...registerNames.map((name, register): [Wire, Binding] => [cells[name], {kind: 'register', register}]),
  ])
  const loop: LoopProgram = {
    positions: projects,
    buffers: [{name: 'users', cellsPerDocument: userCells}],
    registers: registerNames.map(name => ({name, initial: 0})),
    fields: [],
    outputGroups: [
      {name: 'counts', kind: 'document', valuesPerDocument: 4, fill: 0},
      {name: 'codes', kind: 'position', valuesPerDocument: projects, fill: 0},
    ],
    stages: [createStage({
      name: 'audit', repeat: 'forward', circuit, sharedOffset: 0, bindings,
      outputs: [
        {wire: code, write: {kind: 'position', group: 1}},
        ...registerNames.map((name, register) => ({wire: next[name], write: {kind: 'register', register} as const})),
      ],
    })],
    results: registerNames.slice(1).map((_, column) => ({group: 0, column, register: column + 1})),
    sharedValues: new Float32Array(initialSource),
    lengthCell: undefined,
  }

  // Writes an org's project and team tables and two policies into the shared values: what a new org or a policy edit
  // uploads, with no new program.
  function writeShared(shared: Float32Array, org: Org, policyA: Uint8Array, policyB: Uint8Array) {
    org.teamOf.forEach((value, index) => (shared[tables.teamOf[index]!] = value))
    org.sharedDomain.forEach((value, index) => (shared[tables.sharedOf[index]!] = value))
    org.plan.forEach((value, index) => (shared[tables.planOf[index]!] = value))
    policyA.forEach((value, index) => (shared[tables.policyA[index]!] = value))
    policyB.forEach((value, index) => (shared[tables.policyB[index]!] = value))
  }
  return {loop, circuit, writeShared}
}

// Every user's cells, as buffer 0 of the loop program.
export function writeUserCells(org: Org): Float32Array {
  const cells = new Float32Array(org.users * userCells)
  for (let user = 0; user < org.users; user++) {
    const base = user * userCells
    for (let slot = 0; slot < membershipSlots; slot++) {
      cells[base + slot] = org.memberTeam[user * membershipSlots + slot]!
      cells[base + membershipSlots + slot] = org.memberRole[user * membershipSlots + slot]!
    }
    cells[base + 2 * membershipSlots] = org.staff[user]!
    cells[base + 2 * membershipSlots + 1] = org.userDomain[user]!
  }
  return cells
}
