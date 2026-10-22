// A datatype law's cyclic proof (core/data.ts) as a theorem about the datatype as declared. Untrusted: Lean checks
// everything this writes. The export (after the proof's facts and nodes, emit.ts's cyclicToLean) is, in a namespace of
// the item's own:
//   - each datatype as a Lean `inductive` (its constructors in core/data.ts's order, fields `Nat` or a datatype), its
//     tag, size and fields as functions, and a bijection with the naturals (`enc`, `dec`, `dec_enc`, `enc_dec`: those of
//     no field their tag, the rest z + m·q + r, q the fields packed by Data.lean's tupk); a group declared together in
//     `mutual` blocks (its inductives, then its sizes, codes, decodings and the two inverses), its decoding well-founded
//     by (group size + 1)·n + its order (core/data.ts's weakOrder: a datatype decoding n at fields up to n after those)
//   - each function by pattern matching, as written (Lean checks the recursion is structural; functions calling each
//     other in one `mutual` block)
//   - the model: each map of the encoding as the meaning the facts say it has (a function's map at a key: the function
//     at the arguments the key pairs, decoded, its value encoded)
//   - that every fact of the proof holds of the model, each by unfolding and cases on the values it reads
//   - the law, about the Lean definitions, from cyclic_sound at the law's node
import type {Cyclic} from '../kernel/cyclic.ts'
import {type Ctor, type Data, type DataLaw, type FieldSort, type Fn, type Program, type X, type Y, ctorMap, divMap, fieldMap, isDataField, modMap, sizeMap, tagMap, weakOrder} from '../core/data.ts'

const name = (s: string) => s.replace(/#(\d+)$/, '_$1').replace(/[^A-Za-z0-9_']/g, '_')
// The function parameters a function reads, through those it calls.
function paramsOf(p: Program): Map<string, string[]> {
  const out = new Map<string, string[]>()
  const of = (f: Fn): string[] => {
    const had = out.get(f.name)
    if (had) return had
    out.set(f.name, [])
    const own = new Set<string>()
    const walk = (t: unknown): void => { if (!t || typeof t !== 'object') return; if (Array.isArray(t)) { t.forEach(walk); return } const o = t as Record<string, unknown>; if (o.op === 'apply') own.add(o.param as string); if (o.op === 'call' && o.fn !== f.name) { const g = p.fns.find(h => h.name === o.fn); if (g) of(g).forEach(x => own.add(x)) } for (const v of Object.values(o)) walk(v) }
    walk(f.body())
    const list = p.params.filter(x => own.has(x))
    out.set(f.name, list)
    return list
  }
  p.fns.forEach(of)
  return out
}

export function dataLean(id: string, law: DataLaw, p: Program, proof: Cyclic, node: number, theorem: string): (ix: (name: string) => number, mx: (map: string) => number) => string {
  return (ix, mx) => {
    const fparams = paramsOf(p)
    const dataOf = (n: string) => p.datas.find(d => d.name === n)!
    const sortLean = (s: unknown) => (s === 'nat' ? 'Nat' : s === 'bool' ? 'Bool' : s === 'int' ? 'Int' : (s as Data).name)
    // An integer's code (core/data.ts's zigzag), and back: Z.enc and Z.dec, defined below where the program reads one.
    const encOf = (s: unknown, v: string) => (s === 'nat' || s === 'bool' ? v : s === 'int' ? `Z.enc ${v}` : `${(s as Data).name}.enc ${v}`)
    // Terms.
    const lx = (x: X, names: Map<string, string>): string => {
      switch (x.op) {
        case 'var': return names.get(x.name) ?? name(x.name)
        case 'nat': return String(x.value)
        case 'add': return `(${lx(x.a, names)} + ${lx(x.b, names)})`
        case 'sub': return `(${lx(x.a, names)} - ${lx(x.b, names)})`
        case 'min': case 'max': return `(${x.op} ${lx(x.a, names)} ${lx(x.b, names)})`
        case 'mul': return `(${x.k} * ${lx(x.a, names)})`
        case 'prod': return `(${lx(x.a, names)} * ${lx(x.b, names)})`
        case 'mod': case 'imod': return `(${lx(x.a, names)} % ${x.k})`
        case 'div': case 'idiv': return `(${lx(x.a, names)} / ${x.k})`
        case 'int': return `(${x.value} : Int)`
        case 'iadd': return `(${lx(x.a, names)} + ${lx(x.b, names)})`
        case 'isub': return `(${lx(x.a, names)} - ${lx(x.b, names)})`
        case 'ineg': return `(-${lx(x.a, names)})`
        case 'imul': return `((${x.k} : Int) * ${lx(x.a, names)})`
        case 'ofnat': return `((${lx(x.a, names)} : Nat) : Int)`
        case 'if': return `(if ${ly(x.c, names)} then ${lx(x.then, names)} else ${lx(x.else, names)})`
        case 'bool': return ly(x.c, names)
        case 'apply': return `(${name(x.param)} ${lx(x.arg, names)})`
        case 'call': return `(${x.fn}${(fparams.get(x.fn) ?? []).map(q => ` ${name(q)}`).join('')}${x.args.map(a => ` ${lx(a, names)}`).join('')})`
        case 'ctor': { const d = dataOf(x.data), c = d.ctors[x.ctor]!; return x.args.length ? `(${d.name}.${c.name}${x.args.map(a => ` ${lx(a, names)}`).join('')})` : `${d.name}.${c.name}` }
        case 'natmatch': return `(match ${lx(x.of, names)} with | 0 => ${lx(x.zero, names)} | ${name(x.pred)} + 1 => ${lx(x.succ, names)})`
        case 'match': {
          const d = dataOf(x.data)
          return `(match ${lx(x.of, names)} with ${x.cases.map((c, j) => `| .${d.ctors[j]!.name}${c.binds.map(b => ` ${name(b)}`).join('')} => ${lx(c.body, names)}`).join(' ')})`
        }
      }
    }
    const ly = (y: Y, names: Map<string, string>): string => {
      switch (y.op) {
        case '<': case '<=': case '=': return `(decide (${lx(y.a, names)} ${y.op === '<=' ? '≤' : y.op} ${lx(y.b, names)}))`
        case 'i<': case 'i<=': return `(decide (${lx(y.a, names)} ${y.op === 'i<=' ? '≤' : '<'} ${lx(y.b, names)}))`
        case 'and': return `(${y.xs.map(z => ly(z, names)).join(' && ')})`
        case 'or': return `(${y.xs.map(z => ly(z, names)).join(' || ')})`
        case 'not': return `(!${ly(y.x, names)})`
        case 'is': return `(decide (${y.data}.tag ${lx(y.of, names)} = ${y.ctor}))`
        case 'holds': return lx(y.x, names)
      }
    }
    // The law as a proposition.
    const lp = (y: Y, names: Map<string, string>): string => {
      switch (y.op) {
        case '<': case '<=': case '=': return `${lx(y.a, names)} ${y.op === '<=' ? '≤' : y.op} ${lx(y.b, names)}`
        case 'i<': case 'i<=': return `${lx(y.a, names)} ${y.op === 'i<=' ? '≤' : '<'} ${lx(y.b, names)}`
        case 'and': return y.xs.map(z => `(${lp(z, names)})`).join(' ∧ ')
        case 'or': return y.xs.length === 2 && y.xs[0]!.op === 'not' ? `(${lp(y.xs[0]!.x, names)}) → (${lp(y.xs[1]!, names)})` : y.xs.map(z => `(${lp(z, names)})`).join(' ∨ ')
        case 'not': return `¬(${lp(y.x, names)})`
        case 'is': return `${y.data}.tag ${lx(y.of, names)} = ${y.ctor}`
        case 'holds': return `${lx(y.x, names)} = true`
      }
    }
    const out: string[] = [`namespace ${id}`, 'open Kern', '']
    // Datatypes, their parts and their codes, a group (declared together) at a time: its inductives, and each family of
    // definitions over it (sizes, codes, decoding, the two inverses) in one `mutual` block when it has several.
    const groups: Data[][] = []
    for (const d of p.datas) { const last = groups.at(-1); if (last && last[0]!.group === d.group) last.push(d); else groups.push([d]) }
    const block = (ds: Data[], each: (d: Data) => string[]): string[] => (ds.length > 1 ? ['mutual', ...ds.flatMap(each), 'end'] : ds.flatMap(each))
    const fieldT = (f: {sort: FieldSort}) => (f.sort === 'nat' ? 'Nat' : f.sort === 'int' ? 'Int' : f.sort.data)
    const inG = (d: Data, f: {sort: FieldSort}) => isDataField(f.sort) && d.group.includes(f.sort.data)
    const fieldEnc = (f: {sort: FieldSort}, v: string) => (f.sort === 'nat' ? v : f.sort === 'int' ? `Z.enc ${v}` : `${f.sort.data}.enc ${v}`)
    const fieldDec = (f: {sort: FieldSort}, v: string) => (f.sort === 'nat' ? v : f.sort === 'int' ? `(Z.dec ${v})` : `(${f.sort.data}.dec ${v})`)
    // The integers' codes, where the program reads an integer: a bijection with the naturals, as a datatype's.
    const usesInt = p.divisors.includes(2) && /"(?:sort|ret)":"int"|"op":"(?:int|iadd|isub|ineg|imul|ofnat|imod|idiv|i<|i<=)"/.test(JSON.stringify([p.datas.map(d => d.ctors), p.fns.map(f => ({params: f.params, ret: f.ret, body: f.body()})), law]))
    if (usesInt) out.push('abbrev Z := Int', 'def Z.enc (z : Int) : Nat := (2 * z).toNat + (-2 * z - 1).toNat',
      'def Z.dec (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -((n / 2 : Nat) : Int) - 1',
      '@[simp] theorem Z.dec_enc (z : Int) : Z.dec (Z.enc z) = z := by unfold Z.dec Z.enc; split <;> omega',
      '@[simp] theorem Z.enc_dec (n : Nat) : Z.enc (Z.dec n) = n := by unfold Z.dec Z.enc; split <;> omega', '')
    const pat = (d: Data, j: number, used: (i: number) => string | undefined) => `.${d.ctors[j]!.name}${d.ctors[j]!.fields.map((_, i) => ` ${used(i) ?? '_'}`).join('')}`
    for (const ds of groups) {
      const mutualG = ds.length > 1, order = mutualG ? weakOrder(ds) : new Map<string, number>()
      // Decoding n reads fields at codes at most (n − z) / m: below n, or (a weak datatype) at most n, whose measure then
      // numbers it after the group's datatypes its fields name.
      const measure = (d: Data) => (mutualG ? `${ds.length + 1} * n + ${order.get(d.name)!}` : 'n')
      const inductive = (d: Data) => [`inductive ${d.name} where`, ...d.ctors.map(c => `  | ${c.name}${c.fields.map(f => ` (${f.name} : ${fieldT(f)})`).join('')} : ${d.name}`)]
      if (mutualG) out.push(...block(ds, inductive), `deriving instance DecidableEq for ${ds.map(d => d.name).join(', ')}`, '')
      else out.push(...inductive(ds[0]!), 'deriving DecidableEq', '')
      for (const d of ds) out.push(`def ${d.name}.tag : ${d.name} → Nat`, ...d.ctors.map((_, j) => `  | ${pat(d, j, () => undefined)} => ${j}`))
      out.push(...block(ds, d => [`def ${d.name}.size : ${d.name} → Nat`, ...d.ctors.map((c, j) => `  | ${pat(d, j, i => (inG(d, c.fields[i]!) ? `x${i}` : undefined))} => 1${c.fields.flatMap((f, i) => (inG(d, f) ? [` + ${fieldT(f)}.size x${i}`] : [])).join('')}`)]))
      const z = (d: Data) => d.nullary, m = (d: Data) => d.ctors.length - d.nullary
      const codeOf = (c: Ctor) => `tupk [${c.fields.map((f, i) => fieldEnc(f, `x${i}`)).join(', ')}]`
      out.push(...block(ds, d => [`def ${d.name}.enc : ${d.name} → Nat`, ...d.ctors.map((c, j) => (j < z(d) ? `  | ${pat(d, j, () => undefined)} => ${j}` : `  | ${pat(d, j, i => `x${i}`)} => ${z(d)} + ${m(d)} * ${codeOf(c)} + ${j - z(d)}`))]))
      for (const d of ds) for (const [j, c] of d.ctors.entries()) for (const [i, f] of c.fields.entries()) out.push(`def ${d.name}.${c.name}_${f.name} : ${d.name} → Nat`, ...d.ctors.map((_, j2) => (j2 === j ? `  | ${pat(d, j2, i2 => (i2 === i ? 'v' : undefined))} => ${fieldEnc(f, 'v')}` : `  | ${pat(d, j2, () => undefined)} => 0`)))
      // dec: those of no field by their number, the rest by z + m·q + r.
      const q = (d: Data) => `((n - ${z(d)}) / ${m(d)})`
      const recCalls = (d: Data) => d.ctors.flatMap(c => c.fields.flatMap((f, i) => (inG(d, f) ? [[c.fields.length, i]] : [])))
      const datCalls = (d: Data) => d.ctors.flatMap(c => c.fields.flatMap((f, i) => (f.sort !== 'nat' ? [[c.fields.length, i, isDataField(f.sort) ? f.sort.data : 'Z'] as const] : [])))
      const wf = (d: Data) => (ds.some(x => recCalls(x).length) ? [`termination_by ${measure(d)}`, ...(recCalls(d).length ? [`decreasing_by all_goals first ${recCalls(d).map(([kk, i]) => `| (have := tup_le ${kk} ${i} ${q(d)}; omega)`).join(' ')}`] : [])] : [])
      out.push(...block(ds, d => {
        const build = (j: number) => { const c = d.ctors[j]!; return `.${c.name}${c.fields.map((f, i) => { const t = `(tup ${q(d)} ${c.fields.length} ${i})`; return ` ${fieldDec(f, t)}` }).join('')}` }
        const nullary = (j: number): string => (j === z(d) - 1 ? `.${d.ctors[j]!.name}` : `if n = ${j} then .${d.ctors[j]!.name} else ${nullary(j + 1)}`)
        const rest = (r: number): string => (r === m(d) - 1 ? build(z(d) + r) : `if h${r + 1} : (n - ${z(d)}) % ${m(d)} = ${r} then ${build(z(d) + r)} else ${rest(r + 1)}`)
        return [`def ${d.name}.dec (n : Nat) : ${d.name} :=\n  ${z(d) ? `if h0 : n < ${z(d)} then ${nullary(0)} else ` : ''}${m(d) ? rest(0) : `.${d.ctors[0]!.name}`}`, ...wf(d)]
      }), '')
      // dec (enc x) = x, by structural induction; enc (dec n) = n, by well-founded recursion on n.
      out.push(...block(ds, d => [`theorem ${d.name}.dec_enc : ∀ x : ${d.name}, ${d.name}.dec (${d.name}.enc x) = x`, ...d.ctors.flatMap((c, j) => {
        if (j < z(d)) return [`  | ${pat(d, j, () => undefined)} => by rw [${d.name}.dec]; simp [${d.name}.enc]`]
        const code = codeOf(c), full = `${z(d)} + ${m(d)} * ${code} + ${j - z(d)}`
        const ihs = c.fields.flatMap((f, i) => (inG(d, f) ? [`have ih${i} := ${fieldT(f)}.dec_enc x${i}`] : []))
        return [`  | ${pat(d, j, i => `x${i}`)} => by`, `    rw [${d.name}.dec]`, ...ihs.map(h => `    ${h}`),
          `    have e1 : (${full} - ${z(d)}) / ${m(d)} = ${code} := by omega`, `    have e2 : (${full} - ${z(d)}) % ${m(d)} = ${j - z(d)} := by omega`,
          `    simp [${d.name}.enc, e1, e2, tupk, tup${c.fields.flatMap((f, i) => (inG(d, f) ? [`, ih${i}`] : [])).join('')}]`]
      })]))
      for (const d of ds) {
        const D = d.name
        out.push(`@[simp] theorem ${D}.dec_enc' (x : ${D}) : ${D}.dec (${D}.enc x) = x := ${D}.dec_enc x`,
          `@[simp] theorem ${D}.enc_inj (a b : ${D}) : ${D}.enc a = ${D}.enc b ↔ a = b := ⟨fun h => by rw [← ${D}.dec_enc a, h, ${D}.dec_enc], fun h => h ▸ rfl⟩`)
        for (let j = 0; j < z(d); j++) out.push(`@[simp] theorem ${D}.dec_${j} : ${D}.dec ${j} = .${d.ctors[j]!.name} := by rw [${D}.dec]; simp`, `@[simp] theorem ${D}.enc_${j} : ${D}.enc .${d.ctors[j]!.name} = ${j} := rfl`)
      }
      out.push(...block(ds, d => [`theorem ${d.name}.enc_dec (n : Nat) : ${d.name}.enc (${d.name}.dec n) = n := by`, `  rw [${d.name}.dec]`, `  repeat' split`, `  all_goals (try simp only [${d.name}.enc])`,
        ...datCalls(d).map(([kk, i, F]) => `  all_goals (try rw [${F}.enc_dec (tup ${q(d)} ${kk} ${i})])`),
        `  all_goals (first | omega | (simp [tupk, tup] <;> omega))`, ...wf(d)]), '')
    }
    // The functions, as declared: those of a ring (calling each other) in one `mutual` block, where its last is.
    const fnDef = (f: Fn) => {
      const names = new Map(f.params.map(q => [`${f.name}.${q.name}`, name(q.name)]))
      return `def ${f.name}${(fparams.get(f.name) ?? []).map(q => ` (${name(q)} : Nat → Nat)`).join('')}${f.params.map(q => ` (${name(q.name)} : ${sortLean(q.sort)})`).join('')} : ${sortLean(f.ret)} :=\n  ${lx(f.body(), names)}`
    }
    for (const [i, f] of p.fns.entries()) {
      const ring = p.fns.filter(g => f.ring.includes(g.name))
      if (ring.length < 2) { out.push(fnDef(f)); continue }
      if (p.fns.slice(i + 1).some(g => f.ring.includes(g.name))) continue
      out.push('mutual', ...ring.map(fnDef), 'end')
    }
    out.push('')
    // The model: each map the proof reads, as its meaning.
    const params = p.params.map(name)
    const pk = (k: string, n: number): string[] => (n === 1 ? [k] : [...pk(`(unpk ${k}).1`, n - 1), `(unpk ${k}).2`])
    const arms: string[] = []
    const arm = (map: string, body: string) => { let j: number; try { j = mx(map) } catch { return } if (j >= 0) arms.push(`  | ${j} => ${body}`) }
    for (const d of p.datas) {
      const D = d.name
      arm(tagMap(D), `${D}.tag (${D}.dec k)`); arm(sizeMap(D), `${D}.size (${D}.dec k)`)
      for (const [j, c] of d.ctors.entries()) {
        c.fields.forEach((f, i) => arm(fieldMap(d, j, i), `${D}.${c.name}_${f.name} (${D}.dec k)`))
        if (c.fields.length) { const as = pk('k', c.fields.length); arm(ctorMap(d, j), `${D}.enc (${D}.${c.name}${c.fields.map((f, i) => ` ${fieldDec(f, as[i]!)}`).join('')})`) }
      }
    }
    for (const f of p.fns) {
      const as = pk('k', f.params.length), call = `(${f.name}${(fparams.get(f.name) ?? []).map(q => ` ${name(q)}`).join('')}${f.params.map((q, i) => (q.sort === 'nat' ? ` ${as[i]}` : q.sort === 'bool' ? ` (${as[i]} = 1)` : q.sort === 'int' ? ` (Z.dec ${as[i]})` : ` (${(q.sort as Data).name}.dec ${as[i]})`)).join('')})`
      arm(f.name, f.ret === 'nat' ? call : f.ret === 'bool' ? `if ${call} then 1 else 0` : encOf(f.ret, call))
    }
    // Division by a constant: Lean's own / and %.
    for (const k2 of p.divisors) { arm(divMap(k2), `k / ${k2}`); arm(modMap(k2), `k % ${k2}`) }
    for (const q of p.params) arm(q, `${name(q)} k`)
    out.push(`noncomputable def model${params.map(q => ` (${q} : Nat → Nat)`).join('')} : Nat → Nat → Nat := fun m k =>\n  match m with\n${arms.join('\n')}\n  | _ => 0`, '')
    // Every fact holds of the model: each key a value (a datatype's, by its code), unfolded, the values' cases.
    const M = `(model${params.map(q => ` ${q}`).join('')})`
    const fnSimp = p.fns.map(f => f.name).join(', ')
    const dataSimp = p.datas.flatMap(d => [`${d.name}.tag`, `${d.name}.size`, ...d.ctors.flatMap(c => c.fields.map(f => `${d.name}.${c.name}_${f.name}`))]).join(', ')
    const sortOfKey = (fact: string, i: number): string => {
      const [kind, what] = [fact.split(' ')[0]!, fact.slice(fact.indexOf(' ') + 1)]
      if (kind === 'shape' || kind === 'eta') return what
      if (kind === 'ctor') { for (const d of p.datas) for (const [j, c] of d.ctors.entries()) if (ctorMap(d, j) === what) { const f = c.fields[i]!; return f.sort === 'nat' ? 'nat' : f.sort === 'int' ? 'Z' : f.sort.data } }
      if (kind === 'fn') { const f = p.fns.find(g => g.name === what)!; const s = f.params[i]!.sort; return s === 'nat' || s === 'bool' ? 'nat' : s === 'int' ? 'Z' : (s as Data).name }
      return 'nat'
    }
    const proofs = proof.facts.map((f, i) => {
      const kind = f.name.split(' ')[0]!
      const ks = `[${f.keys.map(ix).join(', ')}]`
      const head = `  · -- ${f.name}\n    simp only [evalC, evalE${f.keys.map(key => `, override_at ${ks} ${ix(key)} (by decide)`).join('')}]`
      if (kind === 'nullary') return `${head}\n    simp [model, ${dataSimp}]`
      if (kind === 'arith') return `${head}\n    (try simp [model]) <;> omega`
      if (kind === 'cong') {
        const n = f.keys.length / 2
        return `${head}\n${f.keys.slice(0, n).map((key, q) => `    by_cases h${q} : vals ${ix(key)} = vals ${ix(f.keys[n + q]!)}`).join('\n')}\n    all_goals simp_all`
      }
      const keys = f.keys.map((key, q) => ({v: ix(key), s: sortOfKey(f.name, q), x: `k${q}`}))
      const obtain = keys.filter(x => x.s !== 'nat').map(x => `    obtain ⟨${x.x}, h${x.x}⟩ : ∃ y : ${x.s}, vals ${x.v} = ${x.s}.enc y := ⟨${x.s}.dec (vals ${x.v}), (${x.s}.enc_dec _).symm⟩`)
      const rw = keys.filter(x => x.s !== 'nat').map(x => `h${x.x}`)
      const depth = 2
      const casePat = (D: string, dd: number): string => { const d = dataOf(D); return dd <= 0 ? '_' : d.ctors.map(c => (c.fields.length ? `⟨${c.fields.map(fl => (isDataField(fl.sort) ? casePat(fl.sort.data, dd - 1) : '_')).join(', ')}⟩` : '_')).join(' | ') }
      // A function recursing on a natural: that argument as 0 or m + 1 (where its match is decided).
      const fnOfFact = kind === 'fn' ? p.fns.find(g => g.name === f.name.slice(3)) : undefined, natDec = fnOfFact?.decreases !== undefined && fnOfFact.params[fnOfFact.decreases]!.sort === 'nat' ? keys[fnOfFact.decreases] : undefined
      const cases = [...(natDec ? [`rcases hn : vals ${natDec.v} with _ | m`] : []), ...keys.filter(x => x.s !== 'nat' && x.s !== 'Z').map(x => `rcases ${x.x} with ${casePat(x.s, depth)}`)]
      void i
      return `${head}\n${obtain.join('\n')}${obtain.length ? '\n' : ''}    simp [${[...rw, 'model', 'unpk_fst', 'unpk_snd', 'unpk_sq_fst', 'unpk_sq_snd', 'unpk_sqb_fst', 'unpk_sqb_snd'].join(', ')}]\n${cases.length ? `    ${cases.join(' <;> ')}\n` : ''}    all_goals (simp [${[fnSimp, dataSimp].filter(Boolean).join(', ')}])\n    all_goals (try split) <;> (try simp_all) <;> (try omega)\n    all_goals (try split) <;> (try simp_all) <;> (try omega)${usesInt ? '\n    all_goals (simp only [Z.enc] at *; (repeat\' split) <;> omega)' : ''}`
    })
    out.push(`theorem facts_hold${params.map(q => ` (${q} : Nat → Nat)`).join('')} (env : Nat → Nat) : FactsHold ${id}_facts env ${M} := by`,
      `  intro fa hfa vals`, `  simp only [${id}_facts, _root_.List.mem_cons, _root_.List.not_mem_nil, or_false] at hfa`,
      `  rcases hfa with ${proof.facts.map(() => 'rfl').join(' | ')}`, ...proofs, '')
    // The law, about the definitions.
    const vars = law.vars, lnames = new Map(vars.map(x => [x.name, name(x.name)]))
    const env = vars.reduceRight((acc, x) => `if i = ${ix(x.name)} then ${encOf(x.sort, name(x.name))} else ${acc}`, '0')
    const nd = `${id}_node${node}`
    out.push(`theorem ${theorem}${params.map(q => ` (${q} : Nat → Nat)`).join('')}${vars.map(x => ` (${name(x.name)} : ${sortLean(x.sort)})`).join('')} :\n    ${lp(law.holds, lnames)} := by`,
      `  have h := ${id}_sound ${M} (fun i => ${env}) (facts_hold${params.map(q => ` ${q}`).join('')} _) _ ${nd}_mem (by simp [${nd}_hyps, ${id}_hyps${node}])`,
      `  rw [${nd}_concl] at h`,
      `  simp [${id}_concl${node}, evalC, evalE, model, unpk_fst, unpk_snd, unpk_sq_fst, unpk_sq_snd, unpk_sqb_fst, unpk_sqb_snd] at h`,
      `  first | simpa using h | (intros; simp_all)${usesInt ? ' | (simp only [Z.enc] at h; (repeat\' split at h) <;> omega)' : ''}`, '', `end ${id}`)
    return out.join('\n')
  }
}
