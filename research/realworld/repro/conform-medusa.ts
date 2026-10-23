// Conformance and repro harness for inventory/medusa/reservations: runs Medusa's ORIGINAL InventoryModuleService
// (@medusajs/inventory@2.22.0 from npm, the release of commit 205aff40bacfa0049e0b9d3a7913a674738bff31, installed into
// a temp dir) against in-memory stand-ins for its storage (the level, reservation and item services and the base
// repository: list/create/update/delete/softDelete/restore with the filters the module passes, a call rolled back
// when it throws, as the module's transaction is), and the rule's interpreter on the same requests.
//   bun research/realworld/repro/conform-medusa.ts            the repro runs, then 300 random runs (or: ... conform-medusa.ts <runs>)
// The storage stand-ins are the only code here that is not Medusa's; they do what Postgres and MikroORM do for these
// calls (a unique (item, location) level, soft-deleted rows filtered out of list, restore clearing deleted_at).
import {execSync} from 'node:child_process'
import {existsSync, mkdirSync, writeFileSync} from 'node:fs'
import {createRequire} from 'node:module'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {reservations} from '../items/invapprove-medusa.ts'

const dir = join(tmpdir(), 'gdp-realworld-medusa-inventory-2.22.0')
export function loadMedusa(): new (deps: Record<string, unknown>, decl: unknown) => Record<string, (...a: unknown[]) => Promise<unknown>> {
  if (!existsSync(join(dir, 'node_modules/@medusajs/inventory'))) {
    mkdirSync(dir, {recursive: true})
    writeFileSync(join(dir, 'package.json'), '{"name":"medusa-repro","private":true}')
    execSync('npm install --ignore-scripts --no-audit --no-fund @medusajs/inventory@2.22.0 @medusajs/framework@2.22.0', {cwd: dir, stdio: 'ignore'})
  }
  return createRequire(join(dir, 'package.json'))('@medusajs/inventory/dist/services/inventory-module').default
}

type Level = {id: string, inventory_item_id: string, location_id: string, stocked_quantity: number, reserved_quantity: number}
type Res = {id: string, inventory_item_id: string, location_id: string, quantity: number, allow_backorder: boolean, deleted: boolean}
const ITEM = 'iitem_1'
const ids = (v: unknown): string[] => (v === undefined ? [] : Array.isArray(v) ? v as string[] : [v as string])

// The original module over in-memory storage.
export function original() {
  const Service = loadMedusa()
  let levels: Level[] = [], res: Res[] = [], n = 0
  const level = (l: Level) => ({...l, available_quantity: l.stocked_quantity - l.reserved_quantity})
  const inventoryLevelService = {
    async list(f: {$or?: Record<string, unknown>[], inventory_item_id?: string, location_id?: string}) {
      const ors = f.$or ?? [f]
      return levels.filter(l => ors.some(o => ('id' in o ? ids(o.id).includes(l.id) : o.inventory_item_id === l.inventory_item_id && o.location_id === l.location_id))).map(level)
    },
    async create(input: Partial<Level>[] | Partial<Level>) {
      const out = []
      for (const i of Array.isArray(input) ? input : [input]) {
        if (levels.some(l => l.inventory_item_id === i.inventory_item_id && l.location_id === i.location_id)) throw new Error('unique violation IDX_inventory_level_location_id_inventory_item_id')
        const l = {id: `ilev_${i.location_id}`, inventory_item_id: i.inventory_item_id!, location_id: i.location_id!, stocked_quantity: Number(i.stocked_quantity ?? 0), reserved_quantity: 0}
        levels.push(l); out.push(level(l))
      }
      return out
    },
    async update(input: (Partial<Level> & {id: string})[] | (Partial<Level> & {id: string})) {
      const out = []
      for (const u of (Array.isArray(input) ? input : [input]).filter(Boolean)) {
        const l = levels.find(x => x.id === u.id)!
        if (u.stocked_quantity !== undefined) l.stocked_quantity = Number(u.stocked_quantity)
        if (u.reserved_quantity !== undefined) l.reserved_quantity = Number(u.reserved_quantity)
        out.push(level(l))
      }
      return Array.isArray(input) ? out : out[0]
    },
  }
  const reservationItemService = {
    async list(f: {id?: unknown}) { return res.filter(r => !r.deleted && ids(f.id).includes(r.id)).map(r => ({...r})) },
    async create(input: Partial<Res>[]) {
      return input.map(i => { const r = {id: `res_${n++}`, inventory_item_id: i.inventory_item_id!, location_id: i.location_id!, quantity: Number(i.quantity), allow_backorder: !!i.allow_backorder, deleted: false}; res.push(r); return {...r} })
    },
    async update(input: (Partial<Res> & {id: string})[]) {
      return input.map(u => {
        const r = res.find(x => x.id === u.id && !x.deleted)!
        if (u.quantity !== undefined) r.quantity = Number(u.quantity)
        if (u.location_id !== undefined) r.location_id = u.location_id
        if (u.allow_backorder !== undefined) r.allow_backorder = u.allow_backorder
        return {...r}
      })
    },
    async delete(keys: unknown) { const k = ids(keys); res = res.filter(r => !k.includes(r.id)) },
    async softDelete(keys: unknown) { const k = ids(keys); for (const r of res) if (k.includes(r.id)) r.deleted = true; return [[], {}] },
    async restore(keys: unknown) {
      const k = (Array.isArray(keys) ? keys : [keys]).flatMap(x => (typeof x === 'object' && x && 'id' in x ? ids((x as {id: unknown}).id) : [x as string]))
      for (const r of res) if (k.includes(r.id)) r.deleted = false
      return [[], {}]
    },
  }
  const baseRepository = {transaction: (f: (m: unknown) => unknown) => f({}), serialize: (x: unknown) => x, getFreshManager: () => ({}), getActiveManager: () => ({})}
  const svc = new Service({baseRepository, inventoryItemService: {}, inventoryLevelService, reservationItemService}, {})
  const ctx = () => ({transactionManager: {}, manager: {}})
  // One call, rolled back if it throws (the module's @InjectTransactionManager transaction).
  async function call(f: () => Promise<unknown>) {
    const saved = JSON.stringify({levels, res, n})
    try { await f(); return true } catch { ({levels, res, n} = JSON.parse(saved)); return false }
  }
  type In = {op: string, loc: number, q: number, back: boolean, q2: number, back2: boolean, id: number, newQ: number | null, newLoc: number | null, newBack: boolean | null, adj: number}
  async function step(i: In) {
    const loc = `sloc_${i.loc}`, rid = `res_${i.id}`
    const r = (location_id: string, quantity: number, allow_backorder: boolean) => ({inventory_item_id: ITEM, location_id, quantity, allow_backorder})
    switch (i.op) {
      case 'level': return call(() => svc.createInventoryLevels_!([{inventory_item_id: ITEM, location_id: loc, stocked_quantity: i.adj}], ctx()))
      case 'create': return call(() => svc.createReservationItems_!([r(loc, i.q, i.back)], ctx()))
      case 'create2': return call(() => svc.createReservationItems_!([r(loc, i.q, i.back), r(loc, i.q2, i.back2)], ctx()))
      case 'update': return call(() => svc.updateReservationItems_!([{id: rid, ...(i.newQ !== null ? {quantity: i.newQ} : {}), ...(i.newLoc !== null ? {location_id: `sloc_${i.newLoc}`} : {}), ...(i.newBack !== null ? {allow_backorder: i.newBack} : {})}], ctx()))
      case 'delete': return call(() => svc.deleteReservationItems_!(rid, ctx()))
      case 'softDelete': return call(() => svc.softDeleteReservationItems_!(rid, {}, ctx()))
      case 'restore': return call(() => svc.restoreReservationItems_!(rid, {}, ctx()))
      case 'adjust': return call(() => svc.adjustInventory_!(ITEM, loc, i.adj, ctx()))
      case 'setStocked': return call(() => svc.updateInventoryLevels_!([{inventory_item_id: ITEM, location_id: loc, stocked_quantity: i.adj}], ctx()))
    }
    throw new Error(i.op)
  }
  const view = () => ({
    next: n,
    Stocked: Object.fromEntries(levels.map(l => [l.location_id.slice(5), l.stocked_quantity])),
    Reserved: Object.fromEntries(levels.map(l => [l.location_id.slice(5), l.reserved_quantity])),
    Res: Object.fromEntries(res.map(x => [x.id.slice(4), x.deleted ? 'deleted' : 'live'])),
    ResQty: Object.fromEntries(res.map(x => [x.id.slice(4), x.quantity])),
    ResLoc: Object.fromEntries(res.map(x => [x.id.slice(4), Number(x.location_id.slice(5))])),
  })
  return {step, view}
}

// The rule's interpreter, viewed the same way (cells of locations and reservations that exist).
export function model() {
  const r = reservations(), m = r.interpreter(), p = r.encodeParams({d: 0})
  let st = m.init(p)
  const blank = {op: 'level', loc: 0, q: 0, back: false, q2: 0, back2: false, id: 0, newQ: null, newLoc: null, newBack: null, adj: 0}
  const cell = (name: string, k: number) => (st.maps[name] as Map<number, number>).get(k) ?? 0
  return {
    step(i: Record<string, unknown>) { st = m.step(p, st, r.encodeInput({...blank, ...i} as typeof blank)) },
    view(locs: string[], resIds: string[]) {
      const d = r.decode(st) as Record<string, Record<string, unknown>> & {next: number}
      const int = (name: string, k: number) => cell(name, k) - cell(`${name}$neg`, k)
      return {
        next: d.next,
        Stocked: Object.fromEntries(locs.map(k => [k, int('Stocked', Number(k))])),
        Reserved: Object.fromEntries(locs.map(k => [k, int('Reserved', Number(k))])),
        Res: Object.fromEntries(resIds.map(k => [k, ['none', 'live', 'deleted'][cell('Res', Number(k))]])),
        ResQty: Object.fromEntries(resIds.map(k => [k, cell('ResQty', Number(k))])),
        ResLoc: Object.fromEntries(resIds.map(k => [k, cell('ResLoc', Number(k))])),
      }
    },
  }
}

const OPS = ['level', 'create', 'create2', 'update', 'delete', 'softDelete', 'restore', 'adjust', 'setStocked']
export async function compareRun(trace: Record<string, unknown>[], print = false) {
  const o = original(), mo = model()
  for (const [k, i] of trace.entries()) {
    const full = {loc: 0, q: 0, back: false, q2: 0, back2: false, id: 0, newQ: null, newLoc: null, newBack: null, adj: 0, ...i} as Parameters<typeof o.step>[0]
    await o.step(full); mo.step(full)
    const ov = o.view(), mv = mo.view(Object.keys(ov.Stocked), Object.keys(ov.Res))
    if (print) console.log(`  ${JSON.stringify(i)}\n    original ${JSON.stringify(ov)}`)
    if (JSON.stringify(ov) !== JSON.stringify(mv)) return {at: k, request: i, original: ov, rule: mv}
  }
  return undefined
}

if (import.meta.main) {
  console.log('repro: a batch of two, each within what is available, reserves more than is stocked')
  await compareRun([{op: 'level', loc: 0, adj: 1}, {op: 'create2', loc: 0, q: 1, q2: 1}], true)
  console.log('repro: moving a reservation to a location with no stock is checked against 0 more, and the old location keeps it')
  await compareRun([{op: 'level', loc: 0, adj: 5}, {op: 'level', loc: 1, adj: 0}, {op: 'create', loc: 0, q: 3}, {op: 'update', id: 0, newLoc: 1}], true)
  console.log('repro: restoring a reservation that is live adds its quantity again')
  await compareRun([{op: 'level', loc: 0, adj: 5}, {op: 'create', loc: 0, q: 2}, {op: 'restore', id: 0}], true)
  let seed = 7
  // mulberry32
  const rand = (n: number) => { seed = (seed + 0x6d2b79f5) | 0; let t = Math.imul(seed ^ (seed >>> 15), 1 | seed); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return (((t ^ (t >>> 14)) >>> 0) % n) }
  const runs = Number(process.argv[2] ?? 300)
  for (let t = 0; t < runs; t++) {
    const trace = Array.from({length: 1 + rand(10)}, () => ({
      op: OPS[rand(OPS.length)], loc: rand(3), q: rand(5), back: rand(3) === 0, q2: rand(5), back2: rand(3) === 0, id: rand(4),
      newQ: rand(3) ? rand(5) : null, newLoc: rand(2) ? rand(3) : null, newBack: rand(3) ? rand(2) === 1 : null, adj: rand(9) - 2,
    }))
    const d = await compareRun(trace)
    if (d) { console.log(`divergence in run ${t}: ${JSON.stringify(trace.slice(0, d.at + 1))}\n  ${JSON.stringify(d)}`); process.exit(1) }
  }
  console.log(`no divergence in ${runs} random runs`)
}
