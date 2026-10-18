// The same enumeration as template.bend, as a Handwired loop program: a document is a block of 2,048 worlds whose high
// atoms are its cells, and a position is one world of the block, whose low 11 atoms are read from shared tables.
import {type Wire} from '../../vendor/handwired/src/runtime/numeric-ui-core.ts'
import {createSourceTable, input, inputBit, list} from '../../vendor/handwired/src/runtime/cells.ts'
import {type Binding, type LoopProgram, createStage} from '../../vendor/handwired/src/json-search/loop-program.ts'
import {type Bit, andNot, bitWire, noneOf, not} from '../../vendor/handwired/src/json-search/regex/bits.ts'

export const lowBits = 11
const block = 1 << lowBits

export function buildEnum(k: number) {
  const high = k - lowBits
  const table = createSourceTable()
  const cells = table.declare({
    highAtoms: list(high, () => inputBit()),
    position: input([0, block], {grid: 1}),
    reachable: input([0, block], {grid: 1}),
    violations: input([0, block], {grid: 1}),
    lowTables: list(lowBits, () => list(block, () => inputBit())),
  })
  const circuit = table.createCircuit()
  const lowAtoms = cells.lowTables.map(column => circuit.indexRead(cells.position, column))
  for (const atom of lowAtoms) {
    circuit.assumeRange(atom, 0, 1)
    circuit.assumeGrid(atom, 1)
  }
  const atom: Wire[] = [...lowAtoms, ...cells.highAtoms]
  const and = (bits: Bit[]): Bit => {
    if (bits.includes(false)) return false
    const wires = bits.filter((b): b is Wire => typeof b !== 'boolean')
    if (wires.length === 0) return true
    if (wires.length === 1) return wires[0]!
    return circuit.reglu([], 1, wires.map(w => [w, 1] as const), 1 - wires.length)
  }
  const or = (bits: Bit[]): Bit => not(circuit, noneOf(circuit, bits))
  // reachable: no odd atom without the even atom below it
  const reach = noneOf(circuit, atom.flatMap((_, i) => (i % 2 === 0 && i + 1 < k ? [andNot(circuit, atom[i + 1]!, atom[i]!)] : [])))
  const clauses: Bit[] = []
  for (let i = 0; i + 2 < k; i += 3) clauses.push(and([atom[i]!, atom[i + 1]!, not(circuit, atom[i + 2]!)]))
  const policy = or(clauses)
  const proposal = or([and([clauses[0]!, atom[k - 1]!]), ...clauses.slice(1)])
  const violation = and([reach, policy, not(circuit, proposal)])
  const next = {
    position: circuit.roundAffine([[cells.position, 1]], 1),
    reachable: circuit.roundAffine([[cells.reachable, 1], [bitWire(circuit, reach), 1]]),
    violations: circuit.roundAffine([[cells.violations, 1], [bitWire(circuit, violation), 1]]),
  }
  const {initialSource} = table.finish()
  const registers = ['position', 'reachable', 'violations'] as const
  const bindings = new Map<Wire, Binding>([
    ...cells.highAtoms.map((wire, column): [Wire, Binding] => [wire, {kind: 'cell', buffer: 0, column}]),
    ...registers.map((name, register): [Wire, Binding] => [cells[name], {kind: 'register', register}]),
  ])
  const shared = new Float32Array(initialSource)
  cells.lowTables.forEach((column, bit) => column.forEach((wire, position) => (shared[wire] = (position >> bit) & 1)))
  const loop: LoopProgram = {
    positions: block,
    buffers: [{name: 'blocks', cellsPerDocument: Math.max(1, high)}],
    registers: registers.map(name => ({name, initial: 0})),
    fields: [],
    outputGroups: [{name: 'counts', kind: 'document', valuesPerDocument: 2, fill: 0}],
    stages: [createStage({
      name: 'enumerate', repeat: 'forward', circuit, sharedOffset: 0, bindings,
      outputs: registers.map((name, register) => ({wire: next[name], write: {kind: 'register', register} as const})),
    })],
    results: [{group: 0, column: 0, register: 1}, {group: 0, column: 1, register: 2}],
    sharedValues: shared,
    lengthCell: undefined,
  }
  return {loop, documents: 2 ** high, cellsPerDocument: Math.max(1, high)}
}

export function writeBlocks(k: number, documents: number, cellsPerDocument: number): Float32Array {
  const cells = new Float32Array(documents * cellsPerDocument)
  for (let d = 0; d < documents; d++) for (let b = 0; b < k - lowBits; b++) cells[d * cellsPerDocument + b] = (d >> b) & 1
  return cells
}
