// Repro for inventory/medusa/reservations' refuted laws: runs Medusa's ORIGINAL InventoryModuleService
// (@medusajs/inventory@2.22.0, installed into a temp dir; see conform-medusa.ts for the storage stand-ins) on the
// counterexamples and prints the levels after each call.
//   bun research/realworld/repro/medusa.ts
import {compareRun} from './conform-medusa.ts'

console.log('1. a batch of two at one location, each within what is available (1), no backorder: reserved 2 > stocked 1')
await compareRun([{op: 'level', loc: 0, adj: 1}, {op: 'create2', loc: 0, q: 1, q2: 1}], true)
console.log('2. moving a reservation of 3 to a location stocked 0: checked against 0 more (the quantity did not change), so the new')
console.log('   location reserves 3 of 0, and the old one keeps its 3 (its -3 adjustment is computed and never applied)')
await compareRun([{op: 'level', loc: 0, adj: 5}, {op: 'level', loc: 1, adj: 0}, {op: 'create', loc: 0, q: 3}, {op: 'update', id: 0, newLoc: 1}], true)
console.log('3. restoring a reservation that is live: listed again and its quantity added again (reserved 4, live reservations 2)')
await compareRun([{op: 'level', loc: 0, adj: 5}, {op: 'create', loc: 0, q: 2}, {op: 'restore', id: 0}], true)
