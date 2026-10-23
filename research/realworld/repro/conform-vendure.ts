// Conformance and repro harness for inventory/vendure/stockMovements: runs Vendure's ORIGINAL StockMovementService,
// StockLevelService, DefaultStockLocationStrategy and StockLocationService's location methods (@vendure/core@2.3.4 from
// npm, the release of commit ff1d8e63533192f264f596ced72e9225ac2127c4, installed into a temp dir) over an in-memory
// stand-in for TypeORM's repositories, and the rule's interpreter on the same requests.
//   bun research/realworld/repro/conform-vendure.ts [runs]      the repro runs, then random runs (default 2000)
// Not Vendure's code here: the repositories (find/findOne/save/update with the `where` the services pass, `In`), one
// stock location, the variant (trackInventory INHERIT) and the global settings (trackInventory = track).
import {execSync} from 'node:child_process'
import {existsSync, mkdirSync, writeFileSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {stockMovements} from '../items/invapprove-vendure.ts'

const dir = join(tmpdir(), 'gdp-realworld-vendure-core-2.3.4')
function req() {
  if (!existsSync(join(dir, 'node_modules/@vendure/core'))) {
    mkdirSync(dir, {recursive: true})
    writeFileSync(join(dir, 'package.json'), '{"name":"vendure-repro","private":true}')
    execSync('npm install --ignore-scripts --no-audit --no-fund @vendure/core@2.3.4', {cwd: dir, stdio: 'ignore'})
  }
  return createRequire(join(dir, 'package.json'))
}

type Row = Record<string, unknown> & {id?: number}
export function original(track: boolean) {
  const require = req()
  require('reflect-metadata')
  const {StockMovementService} = require('@vendure/core/dist/service/services/stock-movement.service')
  const {StockLevelService} = require('@vendure/core/dist/service/services/stock-level.service')
  const {StockLocationService} = require('@vendure/core/dist/service/services/stock-location.service')
  const {DefaultStockLocationStrategy} = require('@vendure/core/dist/config/catalog/default-stock-location-strategy')
  const tables = new Map<string, Row[]>()
  let nextId = 1
  const table = (e: {name: string}) => { if (!tables.has(e.name)) tables.set(e.name, []); return tables.get(e.name)! }
  const matches = (row: Row, where: Record<string, unknown>): boolean => Object.entries(where).every(([k, w]) => {
    // TypeORM's In(...) is a FindOperator with _type 'in' and _value the list.
    const v = w
    if (v && typeof v === 'object' && (v as {_type?: string})._type === 'in') return ((v as {_value: unknown[]})._value).map(String).includes(String(row[k]))
    if (v && typeof v === 'object') return matches((row[k] ?? {}) as Row, v as Record<string, unknown>) || (k === 'orderLine' && String(row.orderLineId) === String((v as {id: unknown}).id))
    return String(row[k]) === String(v)
  })
  const repo = (e: {name: string}) => ({
    async findOne({where}: {where: Record<string, unknown>}) { return table(e).find(r => matches(r, where)) ?? null },
    async find(opts?: {where?: Record<string, unknown>}) { return table(e).filter(r => !opts?.where || matches(r, opts.where)) },
    async save(x: Row | Row[]) {
      for (const o of Array.isArray(x) ? x : [x]) {
        if (o.id === undefined) o.id = nextId++
        if (o.orderLine && typeof o.orderLine === 'object') o.orderLineId = (o.orderLine as Row).id
        if (o.stockLocation && typeof o.stockLocation === 'object') o.stockLocationId = (o.stockLocation as Row).id
        if (!table(e).includes(o)) table(e).push(o)
      }
      return x
    },
    async update(id: number, patch: Row) { Object.assign(table(e).find(r => r.id === id)!, patch) },
  })
  const location = {id: 1, name: 'default'}
  const variant = {id: 1, trackInventory: 'INHERIT'}
  const connection = {
    getRepository: (_ctx: unknown, e: {name: string}) => repo(e),
    async getEntityOrThrow(_ctx: unknown, e: {name: string}, id: unknown) {
      if (e.name === 'ProductVariant') return variant
      return table(e).find(r => String(r.id) === String(id)) ?? (() => { throw new Error(`no ${e.name} ${String(id)}`) })()
    },
  }
  const strategy = new DefaultStockLocationStrategy()
  strategy.init({get: () => connection})
  const configService = {catalogOptions: {stockLocationStrategy: strategy}}
  const locations = Object.create(StockLocationService.prototype)
  Object.assign(locations, {configService, getAllStockLocations: async () => [location], defaultStockLocation: async () => location})
  const levels = new StockLevelService(connection, locations, configService)
  const svc = new StockMovementService(connection, {}, {getSettings: async () => ({trackInventory: track})}, levels, {publish: async () => {}}, locations, configService)
  const ctx = {}
  async function line(id: number) {
    const lines = table({name: 'OrderLine'})
    if (!lines.some(l => l.id === id)) lines.push({id, productVariantId: 1, productVariant: variant, quantity: 0})
  }
  async function step(i: {op: string, line: number, q: number, n: number}) {
    await line(i.line + 1000)
    const lines = [{orderLineId: i.line + 1000, quantity: i.q}]
    if (i.op === 'adjust') await svc.adjustProductVariantStock(ctx, 1, i.n)
    if (i.op === 'allocate') await svc.createAllocationsForOrderLines(ctx, lines)
    if (i.op === 'sale') await svc.createSalesForOrder(ctx, lines)
    if (i.op === 'cancel') await svc.createCancellationsForOrderLines(ctx, lines)
    if (i.op === 'release') await svc.createReleasesForOrderLines(ctx, lines)
  }
  const view = () => {
    const l = table({name: 'StockLevel'})[0] as {stockOnHand: number, stockAllocated: number} | undefined
    return {onHand: l?.stockOnHand ?? 0, allocated: l?.stockAllocated ?? 0}
  }
  return {step, view}
}

export function model(track: boolean) {
  const r = stockMovements(), m = r.interpreter(), p = r.encodeParams({track, d: 0})
  let st = m.init(p)
  return {
    step(i: {op: string, line: number, q: number, n: number}) { st = m.step(p, st, r.encodeInput(i)) },
    view() { const d = r.decode(st) as {onHand: number, allocated: number}; return {onHand: d.onHand, allocated: d.allocated} },
  }
}

export async function compareRun(track: boolean, trace: {op: string, line: number, q: number, n: number}[], print = false) {
  const o = original(track), mo = model(track)
  for (const [k, i] of trace.entries()) {
    await o.step(i); mo.step(i)
    const ov = o.view(), mv = mo.view()
    if (print) console.log(`  ${JSON.stringify(i)} -> original ${JSON.stringify(ov)}`)
    if (JSON.stringify(ov) !== JSON.stringify(mv)) return {at: k, request: i, original: ov, rule: mv}
  }
  return undefined
}

if (import.meta.main) {
  const D = {line: 0, q: 0, n: 0}
  console.log('repro: stock 5, allocate 1 for a line, then release it twice: stockAllocated goes to -1')
  await compareRun(true, [{...D, op: 'adjust', n: 5}, {...D, op: 'allocate', q: 1}, {...D, op: 'release', q: 1}, {...D, op: 'release', q: 1}], true)
  console.log('repro: allocate 1, sell it, then release it: the sale and the release both free the same allocation')
  await compareRun(true, [{...D, op: 'adjust', n: 5}, {...D, op: 'allocate', q: 1}, {...D, op: 'sale', q: 1}, {...D, op: 'release', q: 1}], true)
  let seed = 11
  // mulberry32
  const rand = (n: number) => { seed = (seed + 0x6d2b79f5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return (((t ^ (t >>> 14)) >>> 0) % n) }
  const runs = Number(process.argv[2] ?? 2000), ops = ['adjust', 'allocate', 'sale', 'cancel', 'release']
  for (let t = 0; t < runs; t++) {
    const track = rand(4) !== 0
    const trace = Array.from({length: 1 + rand(10)}, () => ({op: ops[rand(5)]!, line: rand(3), q: rand(5), n: rand(9) - 2}))
    const d = await compareRun(track, trace)
    if (d) { console.log(`divergence (track ${track}): ${JSON.stringify(trace.slice(0, d.at + 1))}\n  ${JSON.stringify(d)}`); process.exit(1) }
  }
  console.log(`no divergence in ${runs} random runs`)
}
