// Conformance and repro harness for payment/medusa/orderItemQuantities: runs Medusa's own order change actions
// (@medusajs/order@2.22.0, the npm release of the pinned commit, installed into a temp dir; never vendored) and the
// rule's interpreter on the same random action sequences, and reports the first divergence. Then it replays the runs
// that refuted the rule's laws on the original, and prints what the original does.
//   bun research/realworld/repro/conform-medusa-order.ts [dir with node_modules/@medusajs/order]
import {execSync} from 'node:child_process'
import {existsSync, mkdtempSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {orderItem} from '../items/ledgerpay-medusa.ts'

let dir = process.argv[2]
if (!dir || !existsSync(join(dir, 'node_modules/@medusajs/order'))) {
  dir = mkdtempSync(join(tmpdir(), 'medusa-order-'))
  // REPRO_VERSION=2.22.1 runs another release (the re-check of 2026-10-24); the rule mirrors 2.22.0.
  const v = process.env.REPRO_VERSION ?? '2.22.0'
  execSync(`npm init -y && npm install @medusajs/order@${v} @medusajs/framework@${v} --no-audit --no-fund --legacy-peer-deps`, {cwd: dir, stdio: 'ignore'})
}
const req = createRequire(join(dir, 'package.json'))
req('@medusajs/order/dist/utils/actions/index.js') // registers every action type
const {OrderChangeProcessing} = req('@medusajs/order/dist/utils/calculate-order-change.js')
const {ChangeActionType} = req('@medusajs/framework/utils')

const ops = ['fulfill', 'ship', 'deliver', 'cancelFulfillment', 'return', 'receive', 'receiveDamaged', 'cancelReturn', 'writeOff', 'reinstate', 'update', 'remove'] as const
const types: Record<(typeof ops)[number], string> = {
  fulfill: ChangeActionType.FULFILL_ITEM, ship: ChangeActionType.SHIP_ITEM, deliver: ChangeActionType.DELIVER_ITEM,
  cancelFulfillment: ChangeActionType.CANCEL_ITEM_FULFILLMENT, return: ChangeActionType.RETURN_ITEM,
  receive: ChangeActionType.RECEIVE_RETURN_ITEM, receiveDamaged: ChangeActionType.RECEIVE_DAMAGED_RETURN_ITEM,
  cancelReturn: ChangeActionType.CANCEL_RETURN_ITEM, writeOff: ChangeActionType.WRITE_OFF_ITEM,
  reinstate: ChangeActionType.REINSTATE_ITEM, update: ChangeActionType.ITEM_UPDATE, remove: ChangeActionType.ITEM_REMOVE,
}
const fields = {fulfilled: 'fulfilled_quantity', shipped: 'shipped_quantity', delivered: 'delivered_quantity', requested: 'return_requested_quantity',
  received: 'return_received_quantity', dismissed: 'return_dismissed_quantity', writtenOff: 'written_off_quantity'} as const
type Item = {quantity: number} & Record<keyof typeof fields, number>
const start = (q0: number): Item => ({quantity: q0, fulfilled: 0, shipped: 0, delivered: 0, requested: 0, received: 0, dismissed: 0, writtenOff: 0})

// One action on the original: an order with the one item, processed by OrderChangeProcessing; a throw keeps the item.
const original = (it: Item, op: (typeof ops)[number], q: number): {item: Item, error?: string} => {
  const detail = Object.fromEntries(Object.entries(fields).map(([k, f]) => [f, it[k as keyof typeof fields]]))
  const order = {id: 'o', items: [{id: 'i', quantity: it.quantity, unit_price: 1, detail: {...detail, quantity: it.quantity}}], shipping_methods: [], total: 0}
  try {
    const p = new OrderChangeProcessing({order, transactions: [], actions: [{action: types[op], details: {reference_id: 'i', quantity: q}}], options: {}})
    p.processActions()
    const i = p.getCurrentOrder().items[0]
    const num = (x: unknown) => Number(typeof x === 'object' && x !== null && 'numeric' in x ? (x as {numeric: number}).numeric : (x ?? 0))
    return {item: {quantity: num(i.quantity), ...Object.fromEntries(Object.entries(fields).map(([k, f]) => [k, num(i.detail[f])])) as Record<keyof typeof fields, number>}}
  } catch (e) { return {item: it, error: (e as Error).message} }
}

const r = orderItem(), run = r.interpreter()
const ruleRun = (q0: number, trace: {op: (typeof ops)[number], q: number}[]) => {
  const params = r.encodeParams({q0})
  let st = run.init(params)
  return trace.map(t => (st = run.step(params, st, r.encodeInput({op: t.op, q: t.q})), r.decode(st) as unknown as Item))
}

let seed = 7
const rand = (n: number) => ((seed = (seed * 1103515245 + 12345) % 2 ** 31), (seed >>> 8) % n)
let failure: string | undefined, runs = 0
for (; runs < 3000 && !failure; runs++) {
  const q0 = rand(6), trace = Array.from({length: 1 + rand(12)}, () => ({op: ops[rand(ops.length)]!, q: rand(9) - 3}))
  const mine = ruleRun(q0, trace)
  let it = start(q0)
  for (let k = 0; k < trace.length; k++) {
    it = original(it, trace[k]!.op, trace[k]!.q).item
    const m = mine[k]!
    const diff = (Object.keys(it) as (keyof Item)[]).filter(f => m[f] !== it[f])
    if (diff.length) { failure = `q0 ${q0}, after ${JSON.stringify(trace.slice(0, k + 1))}: ${diff.map(f => `${f} original ${it[f]} rule ${m[f]}`).join(', ')}`; break }
  }
}
console.log(failure ? `DIVERGES ${failure}` : `conforms: ${runs} random runs, every part equal after every action`)

// The refuting runs (the search's, shortened by hand to the steps that matter), on the original.
const replay = (name: string, q0: number, trace: {op: (typeof ops)[number], q: number}[]) => {
  let it = start(q0)
  console.log(`\n${name} (q0 = ${q0})`)
  for (const t of trace) { const o = original(it, t.op, t.q); it = o.item; console.log(`  ${t.op}(${t.q}) -> ${o.error ? `refused: ${o.error}` : JSON.stringify(it)}`) }
}
replay('never more shipped than fulfilled', 2, [{op: 'fulfill', q: 1}, {op: 'ship', q: 1}, {op: 'cancelFulfillment', q: 1}])
replay('never more delivered than fulfilled', 2, [{op: 'fulfill', q: 1}, {op: 'deliver', q: 1}, {op: 'cancelFulfillment', q: 1}])
replay('never more returned than fulfilled (positive quantities)', 1, [{op: 'fulfill', q: 1}, {op: 'return', q: 1}, {op: 'receive', q: 1}, {op: 'return', q: 1}, {op: 'receive', q: 1}])
replay('never more returned than fulfilled (the search: a negative cancel)', 2, [{op: 'cancelReturn', q: -2}])
replay('never more written off than ordered (positive quantities)', 2, [{op: 'writeOff', q: 2}, {op: 'writeOff', q: 2}])
replay('never more written off than ordered (the search: a negative reinstate)', 2, [{op: 'reinstate', q: -3}])
