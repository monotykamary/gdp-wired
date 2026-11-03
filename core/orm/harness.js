// The checker imports the original module; only its injected database client is replaced.
import {openSync, readSync, writeSync} from 'node:fs'
import {pathToFileURL} from 'node:url'
const input = openSync(process.argv[2], 'r'), output = openSync(process.argv[3], 'w')
let pending = '', config, mod, next = 0
const objects = new Map()
function line() { for (;;) { const i = pending.indexOf('\n'); if (i >= 0) { const s = pending.slice(0, i); pending = pending.slice(i + 1); return s } const b = Buffer.alloc(65536), n = readSync(input, b, 0, b.length, null); if (!n) return; pending += b.subarray(0, n).toString() } }
const decode = x => x && 'in' in x ? x.in : x && x.none ? null : undefined
const tag = x => typeof x === 'number' ? {n: String(x)} : typeof x === 'string' ? {s: x} : x === undefined ? null : x
async function run(q) {
  if (q.op === 'hello') { config = q; mod = await import(pathToFileURL(q.path).href); return {ok: true} }
  const leaf = config.leaves.find(l => l.orm), meta = leaf?.orm
  if (!leaf) throw Error('ORM table missing')
  if (q.op === 'new' || q.op === 'at') {
    const rows = new Map()
    const state = q.state ?? {}
    if (Object.keys(state).some(k => k !== leaf.name)) throw Error('unexpected state field')
    const cells = state[leaf.name] ?? {}
    if (!cells || typeof cells !== 'object' || Array.isArray(cells)) throw Error('invalid ORM table')
    const fields = meta.fields.filter(f => f.name !== meta.key)
    for (const [k, cell] of Object.entries(cells)) {
      if (!cell || typeof cell !== 'object' || Array.isArray(cell) || Object.keys(cell).length !== fields.length || fields.some(f => !Object.hasOwn(cell, f.name))) throw Error('invalid ORM cell fields')
      const row = Object.create(null)
      row[meta.key] = leaf.key === 'num' ? Number(k) : k
      for (const f of fields) row[f.name] = f.t.k === 'int' ? Number(cell[f.name]) : cell[f.name]
      rows.set(k, row)
    }
    const id = ++next; objects.set(id, {rows, services: new Map()}); return {id}
  }
  if (q.op === 'coverage') return {hit: []}
  const obj = objects.get(q.id); if (!obj) throw Error('unknown object')
  const {rows, services} = obj
  if (q.op === 'get') {
    const cells = Object.create(null)
    for (const [k, row] of rows) { const c = Object.create(null); for (const f of meta.fields) if (f.name !== meta.key) c[f.name] = f.t.k === 'int' ? String(row[f.name]) : row[f.name]; cells[k] = c }
    return {state: {[leaf.name]: cells}}
  }
  if (q.op === 'call') {
    const lookup = where => rows.get(String(where[meta.key]))
    const repo = {
      async findUnique({where}) { const row = lookup(where); return row ? {...row} : null },
      async findOneBy(where) { const row = lookup(where); return row ? {...row} : null },
      async create({data}) { const k = String(data[meta.key]); if (rows.has(k)) throw Error('duplicate key'); rows.set(k, {...data}); return {...data} },
      async update({where, data}) { const row = lookup(where); if (!row) throw Error('missing row'); Object.assign(row, data); return {...row} },
      async save(data) { const k = String(data[meta.key]); rows.set(k, {...data}); return {...data} },
    }
    const db = config.kind === 'prisma' ? {[config.model[0].toLowerCase() + config.model.slice(1)]: repo} : repo
    try {
      const parts = q.m.split('.')
      let receiver, fn
      if (parts.length === 1) fn = mod[parts[0]]
      else if (parts.length === 2) {
        if (!services.has(parts[0])) services.set(parts[0], new mod[parts[0]]())
        receiver = services.get(parts[0]); fn = receiver[parts[1]]
      } else throw Error('invalid entry')
      return {out: tag(await fn.call(receiver, db, ...q.a.map(a => decode(a[1]))))}
    } catch (e) { return {err: String(e)} }
  }
  throw Error(`unknown operation ${q.op}`)
}
for (;;) { const l = line(); if (l === undefined) break; let out; try { out = await run(JSON.parse(l)) } catch (e) { out = {error: String(e)} } writeSync(output, JSON.stringify(out) + '\n') }
