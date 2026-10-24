// Re-check (2026-10-24) of inventory/vendure/stockMovements' suspected bug on the latest release, @vendure/core@3.8.1
// (npm, installed into a temp dir; never vendored): repro/conform-vendure.ts (which runs 2.3.4, the release the rule
// mirrors) with the stand-ins 3.x needs: connection.withTransaction, Repository.increment and the clamp's conditional
// update, the stock level service's row locks taken as plain reads (one process, no concurrency), its request cache and
// the global settings (trackInventory = track, outOfStockThreshold 0), and an order on each line.
//   bun research/realworld/repro/recheck/vendure-stock-3.8.1.ts [runs]
// What it shows on 3.8.1: a second release of a line no longer takes stockAllocated below 0 (the clamp of 92e4f356,
// GHSA-8ghm-q833-cmgp), but it still frees stock the line no longer holds: two lines allocate 1 each, line 0 is released
// twice, and stockAllocated is 0 while line 1 still holds its 1. The random runs then diverge from the rule, which
// mirrors 2.3.4: 3.8.1 allocates at most what is available (default-stock-location-strategy.ts forAllocation).
import {execSync} from 'node:child_process'
import {existsSync, mkdirSync, writeFileSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {stockMovements} from '../../items/invapprove-vendure.ts'

const dir = join(tmpdir(), 'gdp-realworld-vendure-core-3.8.1')
function req() {
  if (!existsSync(join(dir, 'node_modules/@vendure/core'))) {
    mkdirSync(dir, {recursive: true})
    writeFileSync(join(dir, 'package.json'), '{"name":"vendure-repro","private":true}')
    execSync('npm install --ignore-scripts --no-audit --no-fund @vendure/core@3.8.1', {cwd: dir, stdio: 'ignore'})
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
    // update(id, patch), and the clamp's update({id, stockAllocated: LessThan(0)}, patch): a row with a negative count.
    async update(where: number | {id: number, stockAllocated?: unknown}, patch: Row): Promise<{affected: number}> {
      const at = typeof where === 'number' ? {id: where} : where
      const rows = table(e).filter(r => r.id === at.id && (at.stockAllocated === undefined || (r.stockAllocated as number) < 0))
      for (const r of rows) Object.assign(r, patch)
      return {affected: rows.length}
    },
    async increment(where: {id: number}, prop: string, change: number) { const r = table(e).find(x => x.id === where.id)!; r[prop] = (r[prop] as number) + change },
  })
  const location = {id: 1, name: 'default'}
  const variant = {id: 1, trackInventory: 'INHERIT', useGlobalOutOfStockThreshold: true, outOfStockThreshold: 0}
  const connection = {
    getRepository: (_ctx: unknown, e: {name: string}) => repo(e),
    withTransaction: async (ctx: unknown, work: (c: unknown) => unknown) => work(ctx),
    async getEntityOrThrow(_ctx: unknown, e: {name: string}, id: unknown) {
      if (e.name === 'ProductVariant') return variant
      return table(e).find(r => String(r.id) === String(id)) ?? (() => { throw new Error(`no ${e.name} ${String(id)}`) })()
    },
  }
  let levels: Record<string, unknown> = {}
  const strategy = new DefaultStockLocationStrategy()
  const gs = {getSettings: async () => ({trackInventory: track, outOfStockThreshold: 0})}
  strategy.init({get: (c: {name: string}) => (c.name === 'GlobalSettingsService' ? gs : c.name === 'StockLevelService' ? levels : connection)})
  const configService = {catalogOptions: {stockLocationStrategy: strategy}}
  const locations = Object.create(StockLocationService.prototype)
  Object.assign(locations, {configService, getAllStockLocations: async () => [location], defaultStockLocation: async () => location})
  levels = new StockLevelService(connection, locations, configService, {get: (_c: unknown, _k: string, f: () => unknown) => f()}, gs)
  const lv = () => table({name: 'StockLevel'}).filter(r => r.productVariantId === 1)
  Object.assign(levels, {lockStockLevelsForVariants: async () => {}, getLockedStockLevelsForVariant: async () => lv(), getStockLevelsForVariant: async () => lv(), getStockLevelLoader: () => ({load: async () => lv()})})
  const svc = new StockMovementService(connection, {}, gs, levels, {publish: async () => {}}, locations)
  const ctx = {}
  async function line(id: number) {
    const lines = table({name: 'OrderLine'})
    if (!lines.some(l => l.id === id)) lines.push({id, productVariantId: 1, productVariant: variant, quantity: 0, order: {id: 1}})
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
  console.log('repro (3.8.1): two lines allocate 1 each, then line 0 is released twice: line 1 still holds 1, stockAllocated 0')
  await compareRun(true, [{...D, op: 'adjust', n: 5}, {...D, op: 'allocate', q: 1}, {...D, line: 1, op: 'allocate', q: 1}, {...D, op: 'release', q: 1}, {...D, op: 'release', q: 1}], true)
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
