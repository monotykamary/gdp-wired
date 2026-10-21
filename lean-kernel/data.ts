// A datatype law's cyclic proof (core/data.ts) as a theorem about the datatype as declared. Untrusted: Lean checks
// everything this writes. The export (after the proof's facts and nodes, emit.ts's cyclicToLean) is, in a namespace of
// the item's own:
//   - each datatype as a Lean `inductive` (its constructors in core/data.ts's order, fields `Nat` or the datatype), its
//     tag, size and fields as functions, and a bijection with the naturals (`enc`, `dec`, `dec_enc`, `enc_dec`: those of
//     no field their tag, the rest z + m·q + r, q the fields packed by Data.lean's tupk)
//   - each function by pattern matching, as written (Lean checks the recursion is structural)
//   - the model: each map of the encoding as the meaning the facts say it has (a function's map at a key: the function
//     at the arguments the key pairs, decoded, its value encoded)
//   - that every fact of the proof holds of the model, each by unfolding and cases on the values it reads
//   - the law, about the Lean definitions, from cyclic_sound at the law's node
import type {Cyclic} from '../kernel/cyclic.ts'
import {type Data, type DataLaw, type Fn, type Program, type X, type Y, ctorMap, fieldMap, sizeMap, tagMap} from '../core/data.ts'

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
    const sortLean = (s: unknown) => (s === 'nat' ? 'Nat' : s === 'bool' ? 'Bool' : (s as Data).name)
    // Terms.
    const lx = (x: X, names: Map<string, string>): string => {
      switch (x.op) {
        case 'var': return names.get(x.name) ?? name(x.name)
        case 'nat': return String(x.value)
        case 'add': return `(${lx(x.a, names)} + ${lx(x.b, names)})`
        case 'sub': return `(${lx(x.a, names)} - ${lx(x.b, names)})`
        case 'min': case 'max': return `(${x.op} ${lx(x.a, names)} ${lx(x.b, names)})`
        case 'mul': return `(${x.k} * ${lx(x.a, names)})`
        case 'if': return `(if ${ly(x.c, names)} then ${lx(x.then, names)} else ${lx(x.else, names)})`
        case 'bool': return ly(x.c, names)
        case 'apply': return `(${name(x.param)} ${lx(x.arg, names)})`
        case 'call': return `(${x.fn}${(fparams.get(x.fn) ?? []).map(q => ` ${name(q)}`).join('')}${x.args.map(a => ` ${lx(a, names)}`).join('')})`
        case 'ctor': { const d = dataOf(x.data), c = d.ctors[x.ctor]!; return x.args.length ? `(${d.name}.${c.name}${x.args.map(a => ` ${lx(a, names)}`).join('')})` : `${d.name}.${c.name}` }
        case 'match': {
          const d = dataOf(x.data)
          return `(match ${lx(x.of, names)} with ${x.cases.map((c, j) => `| .${d.ctors[j]!.name}${c.binds.map(b => ` ${name(b)}`).join('')} => ${lx(c.body, names)}`).join(' ')})`
        }
      }
    }
    const ly = (y: Y, names: Map<string, string>): string => {
      switch (y.op) {
        case '<': case '<=': case '=': return `(decide (${lx(y.a, names)} ${y.op === '<=' ? '≤' : y.op} ${lx(y.b, names)}))`
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
        case 'and': return y.xs.map(z => `(${lp(z, names)})`).join(' ∧ ')
        case 'or': return y.xs.length === 2 && y.xs[0]!.op === 'not' ? `(${lp(y.xs[0]!.x, names)}) → (${lp(y.xs[1]!, names)})` : y.xs.map(z => `(${lp(z, names)})`).join(' ∨ ')
        case 'not': return `¬(${lp(y.x, names)})`
        case 'is': return `${y.data}.tag ${lx(y.of, names)} = ${y.ctor}`
        case 'holds': return `${lx(y.x, names)} = true`
      }
    }
    const out: string[] = [`namespace ${id}`, 'open Kern', '']
    // Datatypes, their parts and their codes.
    for (const d of p.datas) {
      const D = d.name, z = d.nullary, m = d.ctors.length - z
      const fieldT = (s: string) => (s === 'nat' ? 'Nat' : D)
      out.push(`inductive ${D} where`, ...d.ctors.map(c => `  | ${c.name}${c.fields.map(f => ` (${f.name} : ${fieldT(f.sort)})`).join('')} : ${D}`), 'deriving DecidableEq', '')
      const pat = (j: number, used: (i: number) => string | undefined) => `.${d.ctors[j]!.name}${d.ctors[j]!.fields.map((_, i) => ` ${used(i) ?? '_'}`).join('')}`
      out.push(`def ${D}.tag : ${D} → Nat`, ...d.ctors.map((_, j) => `  | ${pat(j, () => undefined)} => ${j}`))
      out.push(`def ${D}.size : ${D} → Nat`, ...d.ctors.map((c, j) => `  | ${pat(j, i => (c.fields[i]!.sort === 'self' ? `x${i}` : undefined))} => 1${c.fields.flatMap((f, i) => (f.sort === 'self' ? [` + ${D}.size x${i}`] : [])).join('')}`))
      out.push(`def ${D}.enc : ${D} → Nat`, ...d.ctors.map((c, j) => (j < z ? `  | ${pat(j, () => undefined)} => ${j}` : `  | ${pat(j, i => `x${i}`)} => ${z} + ${m} * tupk [${c.fields.map((f, i) => (f.sort === 'nat' ? `x${i}` : `${D}.enc x${i}`)).join(', ')}] + ${j - z}`)))
      for (const [j, c] of d.ctors.entries()) for (const [i, f] of c.fields.entries()) out.push(`def ${D}.${c.name}_${f.name} : ${D} → Nat`, ...d.ctors.map((_, j2) => (j2 === j ? `  | ${pat(j2, i2 => (i2 === i ? 'v' : undefined))} => ${f.sort === 'nat' ? 'v' : `${D}.enc v`}` : `  | ${pat(j2, () => undefined)} => 0`)))
      // dec: those of no field by their number, the rest by z + m·q + r.
      const q = `((n - ${z}) / ${m})`
      const build = (j: number) => { const c = d.ctors[j]!; return `.${c.name}${c.fields.map((f, i) => { const t = `(tup ${q} ${c.fields.length} ${i})`; return f.sort === 'nat' ? ` ${t}` : ` (${D}.dec ${t})` }).join('')}` }
      const nullary = (j: number): string => (j === z - 1 ? `.${d.ctors[j]!.name}` : `if n = ${j} then .${d.ctors[j]!.name} else ${nullary(j + 1)}`)
      const rest = (r: number): string => (r === m - 1 ? build(z + r) : `if h${r + 1} : (n - ${z}) % ${m} = ${r} then ${build(z + r)} else ${rest(r + 1)}`)
      const recCalls = d.ctors.flatMap(c => c.fields.flatMap((f, i) => (f.sort === 'self' ? [[c.fields.length, i]] : [])))
      const dec = `def ${D}.dec (n : Nat) : ${D} :=\n  ${z ? `if h0 : n < ${z} then ${nullary(0)} else ` : ''}${m ? rest(0) : `.${d.ctors[0]!.name}`}`
      out.push(dec, ...(recCalls.length ? ['termination_by n', `decreasing_by all_goals first ${recCalls.map(([kk, i]) => `| (have := tup_le ${kk} ${i} ${q}; omega)`).join(' ')}`] : []), '')
      // dec (enc x) = x, by structural induction; enc (dec n) = n, by well-founded recursion on n.
      out.push(`theorem ${D}.dec_enc : ∀ x : ${D}, ${D}.dec (${D}.enc x) = x`)
      for (const [j, c] of d.ctors.entries()) {
        if (j < z) { out.push(`  | ${pat(j, () => undefined)} => by rw [${D}.dec]; simp [${D}.enc]`); continue }
        const code = `tupk [${c.fields.map((f, i) => (f.sort === 'nat' ? `x${i}` : `${D}.enc x${i}`)).join(', ')}]`, full = `${z} + ${m} * ${code} + ${j - z}`
        const ihs = c.fields.flatMap((f, i) => (f.sort === 'self' ? [`have ih${i} := ${D}.dec_enc x${i}`] : []))
        out.push(`  | ${pat(j, i => `x${i}`)} => by`, `    rw [${D}.dec]`, ...ihs.map(h => `    ${h}`),
          `    have e1 : (${full} - ${z}) / ${m} = ${code} := by omega`, `    have e2 : (${full} - ${z}) % ${m} = ${j - z} := by omega`,
          `    simp [${D}.enc, e1, e2, tupk, tup${c.fields.flatMap((f, i) => (f.sort === 'self' ? [`, ih${i}`] : [])).join('')}]`)
      }
      out.push(`@[simp] theorem ${D}.dec_enc' (x : ${D}) : ${D}.dec (${D}.enc x) = x := ${D}.dec_enc x`,
        `@[simp] theorem ${D}.enc_inj (a b : ${D}) : ${D}.enc a = ${D}.enc b ↔ a = b := ⟨fun h => by rw [← ${D}.dec_enc a, h, ${D}.dec_enc], fun h => h ▸ rfl⟩`)
      for (let j = 0; j < z; j++) out.push(`@[simp] theorem ${D}.dec_${j} : ${D}.dec ${j} = .${d.ctors[j]!.name} := by rw [${D}.dec]; simp`, `@[simp] theorem ${D}.enc_${j} : ${D}.enc .${d.ctors[j]!.name} = ${j} := rfl`)
      out.push(`theorem ${D}.enc_dec (n : Nat) : ${D}.enc (${D}.dec n) = n := by`, `  rw [${D}.dec]`, `  repeat' split`, `  all_goals (try simp only [${D}.enc])`)
      for (const [kk, i] of recCalls) out.push(`  all_goals (try rw [${D}.enc_dec (tup ${q} ${kk} ${i})])`)
      out.push(`  all_goals (first | omega | (simp [tupk, tup]; omega))`, ...(recCalls.length ? ['termination_by n', `decreasing_by all_goals first ${recCalls.map(([kk, i]) => `| (have := tup_le ${kk} ${i} ${q}; omega)`).join(' ')}`] : []), '')
    }
    // The functions, as declared.
    for (const f of p.fns) {
      const names = new Map(f.params.map(q => [`${f.name}.${q.name}`, name(q.name)]))
      out.push(`def ${f.name}${(fparams.get(f.name) ?? []).map(q => ` (${name(q)} : Nat → Nat)`).join('')}${f.params.map(q => ` (${name(q.name)} : ${sortLean(q.sort)})`).join('')} : ${sortLean(f.ret)} :=\n  ${lx(f.body(), names)}`)
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
        if (c.fields.length) { const as = pk('k', c.fields.length); arm(ctorMap(d, j), `${D}.enc (${D}.${c.name}${c.fields.map((f, i) => (f.sort === 'nat' ? ` ${as[i]}` : ` (${D}.dec ${as[i]})`)).join('')})`) }
      }
    }
    for (const f of p.fns) {
      const as = pk('k', f.params.length), call = `(${f.name}${(fparams.get(f.name) ?? []).map(q => ` ${name(q)}`).join('')}${f.params.map((q, i) => (q.sort === 'nat' ? ` ${as[i]}` : q.sort === 'bool' ? ` (${as[i]} = 1)` : ` (${(q.sort as Data).name}.dec ${as[i]})`)).join('')})`
      arm(f.name, f.ret === 'nat' ? call : f.ret === 'bool' ? `if ${call} then 1 else 0` : `${(f.ret as Data).name}.enc ${call}`)
    }
    for (const q of p.params) arm(q, `${name(q)} k`)
    out.push(`noncomputable def model${params.map(q => ` (${q} : Nat → Nat)`).join('')} : Nat → Nat → Nat := fun m k =>\n  match m with\n${arms.join('\n')}\n  | _ => 0`, '')
    // Every fact holds of the model: each key a value (a datatype's, by its code), unfolded, the values' cases.
    const M = `(model${params.map(q => ` ${q}`).join('')})`
    const fnSimp = p.fns.map(f => f.name).join(', ')
    const dataSimp = p.datas.flatMap(d => [`${d.name}.tag`, `${d.name}.size`, ...d.ctors.flatMap(c => c.fields.map(f => `${d.name}.${c.name}_${f.name}`))]).join(', ')
    const sortOfKey = (fact: string, i: number): string => {
      const [kind, what] = [fact.split(' ')[0]!, fact.slice(fact.indexOf(' ') + 1)]
      if (kind === 'shape' || kind === 'eta') return what
      if (kind === 'ctor') { for (const d of p.datas) for (const [j, c] of d.ctors.entries()) if (ctorMap(d, j) === what) return c.fields[i]!.sort === 'nat' ? 'nat' : d.name }
      if (kind === 'fn') { const f = p.fns.find(g => g.name === what)!; const s = f.params[i]!.sort; return s === 'nat' || s === 'bool' ? 'nat' : (s as Data).name }
      return 'nat'
    }
    const proofs = proof.facts.map((f, i) => {
      const kind = f.name.split(' ')[0]!
      const ks = `[${f.keys.map(ix).join(', ')}]`
      const head = `  · -- ${f.name}\n    simp only [evalC, evalE${f.keys.map(key => `, override_at ${ks} ${ix(key)} (by decide)`).join('')}]`
      if (kind === 'nullary') return `${head}\n    simp [model, ${dataSimp}]`
      if (kind === 'cong') {
        const n = f.keys.length / 2
        return `${head}\n${f.keys.slice(0, n).map((key, q) => `    by_cases h${q} : vals ${ix(key)} = vals ${ix(f.keys[n + q]!)}`).join('\n')}\n    all_goals simp_all`
      }
      const keys = f.keys.map((key, q) => ({v: ix(key), s: sortOfKey(f.name, q), x: `k${q}`}))
      const obtain = keys.filter(x => x.s !== 'nat').map(x => `    obtain ⟨${x.x}, h${x.x}⟩ : ∃ y : ${x.s}, vals ${x.v} = ${x.s}.enc y := ⟨${x.s}.dec (vals ${x.v}), (${x.s}.enc_dec _).symm⟩`)
      const rw = keys.filter(x => x.s !== 'nat').map(x => `h${x.x}`)
      const depth = 2
      const casePat = (D: string, dd: number): string => { const d = dataOf(D); return dd <= 0 ? '_' : d.ctors.map(c => (c.fields.length ? `⟨${c.fields.map(fl => (fl.sort === 'self' ? casePat(D, dd - 1) : '_')).join(', ')}⟩` : '_')).join(' | ') }
      const cases = keys.filter(x => x.s !== 'nat').map(x => `rcases ${x.x} with ${casePat(x.s, depth)}`)
      void i
      return `${head}\n${obtain.join('\n')}${obtain.length ? '\n' : ''}    simp [${[...rw, 'model', 'unpk_fst', 'unpk_snd', 'unpk_sq_fst', 'unpk_sq_snd', 'unpk_sqb_fst', 'unpk_sqb_snd'].join(', ')}]\n${cases.length ? `    ${cases.join(' <;> ')}\n` : ''}    all_goals (simp [${[fnSimp, dataSimp].filter(Boolean).join(', ')}])\n    all_goals (try split) <;> (try simp_all) <;> (try omega)`
    })
    out.push(`theorem facts_hold${params.map(q => ` (${q} : Nat → Nat)`).join('')} (env : Nat → Nat) : FactsHold ${id}_facts env ${M} := by`,
      `  intro fa hfa vals`, `  simp only [${id}_facts, _root_.List.mem_cons, _root_.List.not_mem_nil, or_false] at hfa`,
      `  rcases hfa with ${proof.facts.map(() => 'rfl').join(' | ')}`, ...proofs, '')
    // The law, about the definitions.
    const vars = law.vars, lnames = new Map(vars.map(x => [x.name, name(x.name)]))
    const env = vars.reduceRight((acc, x) => `if i = ${ix(x.name)} then ${x.sort === 'nat' || x.sort === 'bool' ? name(x.name) : `${(x.sort as Data).name}.enc ${name(x.name)}`} else ${acc}`, '0')
    const nd = `${id}_node${node}`
    out.push(`theorem ${theorem}${params.map(q => ` (${q} : Nat → Nat)`).join('')}${vars.map(x => ` (${name(x.name)} : ${sortLean(x.sort)})`).join('')} :\n    ${lp(law.holds, lnames)} := by`,
      `  have h := ${id}_sound ${M} (fun i => ${env}) (facts_hold${params.map(q => ` ${q}`).join('')} _) _ ${nd}_mem (by simp [${nd}_hyps, ${id}_hyps${node}])`,
      `  rw [${nd}_concl] at h`,
      `  simp [${id}_concl${node}, evalC, evalE, model, unpk_fst, unpk_snd, unpk_sq_fst, unpk_sq_snd, unpk_sqb_fst, unpk_sqb_snd] at h`,
      `  first | simpa using h | (intros; simp_all)`, '', `end ${id}`)
    return out.join('\n')
  }
}
