// Re-check (2026-10-24) of payment/vendure/orderProcess's suspected bug on the latest release, @vendure/core@3.8.1 (npm,
// installed into a temp dir; never vendored): repro/conform-vendure-order.ts (which runs 2.2.7, the release the rule
// mirrors) with stand-ins for what 3.x's default order process also reads on the way to ArrangingPayment (the order
// service's price adjustments and eligible shipping methods, the stock allocation strategy, the stock level locks), all
// no-ops that refuse nothing. The rule conforms to 3.8.1 on the random runs, and the replay still cancels a placed order
// with a live line from ArrangingAdditionalPayment (default-order-process.ts:287-289 at aba3e9c).
//   bun research/realworld/repro/recheck/vendure-order-3.8.1.ts [dir with node_modules/@vendure/core]
import {execSync} from 'node:child_process'
import {existsSync, mkdtempSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {orderProcess} from '../../items/ledgerpay-vendure.ts'

let dir = process.argv[2]
if (!dir || !existsSync(join(dir, 'node_modules/@vendure/core'))) {
  dir = mkdtempSync(join(tmpdir(), 'vendure-core-'))
  execSync('npm init -y && npm install @vendure/core@3.8.1 --no-audit --no-fund --legacy-peer-deps', {cwd: dir, stdio: 'ignore'})
}
const req = createRequire(join(dir, 'package.json'))
req('reflect-metadata')
const {configureDefaultOrderProcess} = req('@vendure/core/dist/config/order/default-order-process.js')
const {OrderStateMachine} = req('@vendure/core/dist/service/helpers/order-state-machine/order-state-machine.js')
const utils = req('@vendure/core/dist/service/helpers/utils/order-utils.js')

type Facts = {mods: {isSettled: boolean}[], variantsFound: number, stock: number, order: any}
let facts: Facts
// The database, as onTransitionStart reads it: modifications, payments, available variants, stock, the order itself.
const repo = (entity: {name: string}) => ({
  find: async () => (entity.name === 'OrderModification' ? facts.mods : facts.order.payments),
  createQueryBuilder: () => { const qb: any = {leftJoin: () => qb, where: () => qb, andWhere: () => qb, getMany: async () => Array.from({length: facts.variantsFound})}; return qb },
})
const connection = {getRepository: (_ctx: unknown, entity: {name: string}) => repo(entity), getEntityOrThrow: async () => facts.order}
const services: Record<string, unknown> = {TransactionalConnection: connection, ProductVariantService: {getSaleableStockLevel: async () => facts.stock}, OrderService: {applyPriceAdjustments: async () => undefined, getEligibleShippingMethods: async () => []}, ConfigService: {orderOptions: {stockAllocationStrategy: {shouldAllocateStock: async () => false}}}, StockLevelService: {lockStockLevelsForVariants: async () => undefined}}
const proc = configureDefaultOrderProcess({})
await proc.init({get: (cls: {name: string}) => services[cls.name] ?? {}})
const osm = new OrderStateMachine({orderOptions: {process: [{transitions: proc.transitions, onTransitionStart: proc.onTransitionStart}]}})
const original = async (state: string, to: string): Promise<string> => {
  const order = {...facts.order, state}
  try { await osm.transition({}, order, to) } catch { return state }
  return order.state
}

let seed = 11
const rand = (n: number) => ((seed = (seed * 1103515245 + 12345) % 2 ** 31), (seed >>> 8) % n)
const pick = <T>(xs: readonly T[]) => xs[rand(xs.length)]!
const payStates = ['Created', 'Authorized', 'Settled', 'Declined', 'Error', 'Cancelled'] as const
const randomFacts = (): Facts => {
  const lines = Array.from({length: rand(4) ? 1 + rand(2) : 0}, (_, i) => ({id: `l${i}`, quantity: rand(4) ? 1 + rand(2) : 0, productVariant: {id: `v${i}`, name: `v${i}`}}))
  const fulfillments = Array.from({length: rand(3)}, () => {
    const f: any = {state: pick(['Pending', 'Shipped', 'Delivered', 'Cancelled'] as const), lines: []}
    f.lines = lines.filter(() => rand(2)).map(l => ({orderLineId: l.id, quantity: rand(3), fulfillment: f}))
    return f
  })
  const payments = Array.from({length: rand(3)}, () => ({state: rand(2) ? pick(['Authorized', 'Settled'] as const) : pick(payStates), amount: rand(6), refunds: rand(3) ? [] : [{total: rand(2)}]}))
  const order = {id: 1, lines, fulfillments, payments, totalWithTax: rand(4), customer: rand(3) ? {id: 1} : undefined, shippingLines: rand(3) ? [{id: 1}] : []}
  return {mods: Array.from({length: rand(2) ? 0 : rand(3)}, () => ({isSettled: !!rand(3)})), variantsFound: rand(2) ? lines.length : rand(lines.length + 1), stock: rand(4) ? 3 : rand(3), order}
}
// The rule's inputs: what onTransitionStart computes from the facts, with Vendure's own functions.
const inputsOf = (f: Facts) => {
  const o = f.order
  return {
    mods: f.mods.length, unsettled: f.mods.filter(m => !m.isSettled).length, total: o.totalWithTax,
    covered: Math.max(0, utils.totalCoveredByPayments(o)), coveredAS: Math.max(0, utils.totalCoveredByPayments(o, ['Authorized', 'Settled'])),
    coveredS: Math.max(0, utils.totalCoveredByPayments(o, 'Settled')), authorized: o.payments.some((p: {state: string}) => p.state === 'Authorized'),
    lines: o.lines.length, variants: f.variantsFound === new Set(o.lines.map((l: {productVariant: {id: string}}) => l.productVariant.id)).size,
    customer: !!o.customer, shipping: o.shippingLines.length > 0, stock: o.lines.every((l: {quantity: number}) => l.quantity <= f.stock),
    allCancelled: utils.orderLinesAreAllCancelled(o), partShipped: utils.orderItemsArePartiallyShipped(o), allShipped: utils.orderItemsAreShipped(o),
    partDelivered: utils.orderItemsArePartiallyDelivered(o), allDelivered: utils.orderItemsAreDelivered(o),
  }
}

const c = orderProcess(), r = c.rule, run = r.interpreter()
const targets = ['AddingItems', 'Draft', 'ArrangingPayment', 'PaymentAuthorized', 'PaymentSettled', 'PartiallyShipped', 'Shipped', 'PartiallyDelivered', 'Delivered', 'Modifying', 'ArrangingAdditionalPayment', 'Cancelled']
let failure: string | undefined, runs = 0, moves = 0
const seen = new Set<string>()
for (; runs < 3000 && !failure; runs++) {
  const params = r.encodeParams({})
  let st = run.init(params), state = 'Created'
  const trace: string[] = []
  for (let k = 0; k < 16 && !failure; k++) {
    facts = randomFacts()
    const next0: string[] = osm.config.transitions[state].to, to = rand(5) && next0.length ? pick(next0) : pick(targets), inputs = inputsOf(facts)
    trace.push(to)
    const next = await original(state, to)
    if (next !== state) { moves++; seen.add(next) }
    if (process.env.DEBUG && runs < 3) console.log(state, to, next)
    st = run.step(params, st, r.encodeInput({event: to, ...inputs}))
    const mine = (r.decode(st) as {state: string}).state
    if (mine !== next) failure = `after ${trace.join(', ')} (facts ${JSON.stringify(inputs)}): original ${next}, rule ${mine}`
    state = next
  }
}
console.log(failure ? `DIVERGES ${failure}` : `conforms: ${runs} random runs of up to 16 requests (${moves} transitions taken, ${seen.size} states reached), the state equal after each`)

// The run that breaks "an order ships only once its payment has settled": authorized, modified, then shipped.
const line = {id: 'l0', quantity: 1, productVariant: {id: 'v0', name: 'v0'}}
const ful: any = {state: 'Shipped', lines: []}
ful.lines = [{orderLineId: 'l0', quantity: 1, fulfillment: ful}]
const base = {id: 1, lines: [line], fulfillments: [] as unknown[], payments: [{state: 'Authorized', amount: 10, refunds: []}], totalWithTax: 10, customer: {id: 1}, shippingLines: [{id: 1}]}
let state = 'Created'
console.log('\nan order ships only once its payment has settled')
for (const [to, order] of [['AddingItems', base], ['ArrangingPayment', base], ['PaymentAuthorized', base], ['Modifying', base], ['Shipped', {...base, fulfillments: [ful]}]] as const) {
  facts = {mods: [], variantsFound: 1, stock: 5, order}
  const next = await original(state, to)
  console.log(`  ${state} -> ${to}: ${next === state ? 'refused' : next}`)
  state = next
}
console.log(`  the order is ${state}; its only payment is Authorized, none Settled`)

// The run that breaks "a placed order is cancelled only with every line cancelled": from ArrangingAdditionalPayment,
// onTransitionStart returns before checkAllItemsBeforeCancel (default-order-process.ts:283-285).
state = 'Created'
console.log('\na placed order is cancelled only with every line cancelled')
for (const to of ['AddingItems', 'ArrangingPayment', 'PaymentAuthorized', 'ArrangingAdditionalPayment', 'Cancelled']) {
  facts = {mods: [], variantsFound: 1, stock: 5, order: base}
  const next = await original(state, to)
  console.log(`  ${state} -> ${to}: ${next === state ? 'refused' : next}`)
  state = next
}
console.log(`  the order is ${state}; its line still has quantity ${line.quantity} (orderLinesAreAllCancelled: ${utils.orderLinesAreAllCancelled(base)})`)
facts = {mods: [], variantsFound: 1, stock: 5, order: base}
console.log(`  for contrast, PaymentAuthorized -> Cancelled: ${(await original('PaymentAuthorized', 'Cancelled')) === 'PaymentAuthorized' ? 'refused' : 'Cancelled'}`)
