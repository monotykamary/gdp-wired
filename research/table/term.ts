// The table's Q3 on one termination task: `bun research/table/term.ts <task> --its|--sv [--sample-ms 8000]`.
//   (ITS: /ari/<task>; SV: /sv/c/<task>.yml's C program through compare/term/c2ari.py.) Prints JSON lines, the last
//   the result.
//   koat     KoAT2 2.7.0's proof of the same ARI text (compare/term/modal_term.py's command, --show-proof, 60 s): its
//            ranking functions per transition (MPRF, location → linear term), for the comparison
//   sample   runs from the entrypoint (its values at random), each step a model of one rule's guard where the run is
//            (Z3 solving it: an input an equation pins, fresh values bounded together, come out as the guard says),
//            some of the rule's free values fixed at random first; rows are the turns (rule, pre, post)
//   columns  per strongly connected component, per location: the argument positions its rules' guards read, closed
//            under the updates (a position whose value flows into one read) — a param nothing reads is no column
//   Q3       KoAT2's way: per transition t of the component, an LP over the sampled turns for a linear rank per
//            location that drops by 1 and is ≥ 0 on t's turns and doesn't rise on the others' still unbounded; checked
//            by Z3 on the rules themselves (with the invariants below where it fails without); t, and every other
//            transition the rank also bounds, removed; until none is left (terminates) or none moves
//   invariants  Q1 + Q2 per location over the sampled states, the largest subset inductive over the rules (Z3)
import {readFileSync, writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {parseAri, isVar, ruleVars, evalInt, evalBool, type Ari, type Sx as ASx} from '../../compare/term/ari.ts'
import {Z3, show, sym, getValues, type Sx} from './z3.ts'
import {grammar, observe, equalities, bounds, boundRels, ranks, differences, smtTerm, type Lin, type Pair, type Row, type Ranking} from './table.ts'

const args = process.argv.slice(2), task = args[0]!, sv = args.includes('--sv')
const opt = (k: string, d: string) => { const i = args.indexOf(k); return i < 0 ? d : args[i + 1]! }
const sampler = opt('--sampler', 'z3'), boxTarget = opt('--target', 'cpu'), twin = args.includes('--twin')
const sampleMs = Number(opt('--sample-ms', '8000')), deadline = Number(opt('--deadline-ms', '200000')), koatSecs = Number(opt('--koat-s', '60'))
const T0 = performance.now(), ms = () => Math.round(performance.now() - T0)
const out: Record<string, unknown> = {task, suite: sv ? 'sv' : 'its'}
const say = (o: object) => console.log(JSON.stringify({stage: 'progress', ms: ms(), ...o}))
const done = (o: object = {}) => { console.log(JSON.stringify({stage: 'result', ms: ms(), ...out, ...o})); process.exit(0) }

// --- the task's ARI text --------------------------------------------------------------------------------------------------
let text = ''
if (sv) {
  const y = `/sv/c/${task}`, yml = readFileSync(y, 'utf8'), f = /^input_files:\s*'?([^'\s]+)'?/m.exec(yml)![1]!
  const p = spawnSync('python3', ['compare/term/c2ari.py', `${y.slice(0, y.lastIndexOf('/'))}/${f}`], {encoding: 'utf8', timeout: 60000})
  if (p.status !== 0) done({error: `c2ari: ${(p.stderr || '').slice(-300)}`})
  text = p.stdout
} else text = readFileSync(opt('--root', '/ari') + '/' + task, 'utf8')
let ari: Ari
try { ari = parseAri(text) } catch (e) { done({error: `parse: ${(e as Error).message}`}) }
// each rule's guard in disjunctive normal form, a rule per disjunct (at most 16; past that the rule as it is): the
// table's rows then say which disjunct a turn took (KoAT2 splits the same way before its ranks)
function dnf(g: ASx, cap = 16): ASx[][] | undefined {
  if (typeof g === 'string') return g === 'true' ? [[]] : g === 'false' ? [] : [[g]]
  const op = g[0], xs = g.slice(1)
  const prod = (a: ASx[][], b: ASx[][]) => { const o: ASx[][] = []; for (const x of a) for (const y of b) o.push([...x, ...y]); return o }
  if (op === 'and') { let acc: ASx[][] | undefined = [[]]; for (const x of xs) { const d = dnf(x, cap); if (!d || !acc) return undefined; acc = prod(acc, d); if (acc.length > cap) return undefined } return acc }
  if (op === 'or') { const o: ASx[][] = []; for (const x of xs) { const d = dnf(x, cap); if (!d) return undefined; o.push(...d); if (o.length > cap) return undefined } return o }
  if (op === 'not') {
    const x = xs[0]!
    if (Array.isArray(x) && x[0] === 'or') return dnf(['and', ...x.slice(1).map(y => ['not', y])], cap)
    if (Array.isArray(x) && x[0] === 'and') return dnf(['or', ...x.slice(1).map(y => ['not', y])], cap)
    if (Array.isArray(x) && x[0] === 'not') return dnf(x[1]!, cap)
    return [[g]]
  }
  if (op === '=>') return dnf(['or', ['not', xs[0]!], xs[1]!], cap)
  return [[g]]
}
const exOf = (s: ASx, bound: string[]): ASx => (typeof s === 'string' ? s : s[0] === 'exists' ? (((s[1] as ASx[][]).forEach(b => bound.push(b[0] as string))), exOf(s[2]!, bound)) : s.map(x => exOf(x, bound)))
const A: Ari = {...ari!, rules: ari!.rules.flatMap(r => {
  const g = exOf(r.guard, []), d = dnf(g)
  return d && d.length ? d.map(c => ({...r, guard: c.length ? ['and', ...c] : 'true'})) : d && !d.length ? [] : [{...r, guard: g}]
})}
out.rules = {given: ari!.rules.length, split: A.rules.length}

// --- KoAT2's proof ------------------------------------------------------------------------------------------------------
const koatName = (s: string) => s.replace(/\^/g, '_hat_').replace(/'/g, '_q_').replace(/\|/g, '')
type KRank = {transition: string, from: string, depth: number, ranks: Record<string, {coefs: Record<number, number>, k: number}>}
const koat: {answer: string, ranks: KRank[], seconds: number, eliminated?: number[]} = {answer: 'none', ranks: [], seconds: 0}
if (koatSecs > 0) {
  writeFileSync('/tmp/k0.ari', text)
  const t0 = performance.now()
  const sh = "sed -e 's/\\^/_hat_/g' -e \"s/'/_q_/g\" -e 's/|//g' /tmp/k0.ari > /tmp/k.ari && koat2 ari-to-koat /tmp/k.ari --output-file /tmp/t.koat > /dev/null && koat2 analyse --termination -i /tmp/t.koat --show-proof"
  const p = spawnSync('timeout', ['-k', '5', String(koatSecs), 'bash', '-c', sh], {encoding: 'utf8', maxBuffer: 1 << 26})
  koat.seconds = Math.round(performance.now() - t0) / 1000
  const o = p.stdout ?? ''
  const w = o.split('\n').map(s => s.trim()).find(s => s === 'Finite' || s === 'Infinite')
  koat.answer = w === 'Finite' ? 'terminates' : w === 'Infinite' ? 'unknown' : p.status === 124 ? 'timeout' : 'error'
  // "MPRF for transition tᵢ: f(X₀) → g(...) :|: ... of depth d:" … "MPRF:" then "• loc: [e1, e2]" lines
  const sub = (s: string) => s.replace(/[₀-₉]/g, c => String(c.charCodeAt(0) - 0x2080))
  // KoAT2 drops the variables that don't contribute and numbers the rest again: X_j after it is the j-th kept argument
  // ("Eliminate variables [a; X₁; X₃] ..." names them in the first numbering)
  const gone = new Set<number>()
  for (const m of o.matchAll(/Eliminate variables \[([^\]]*)\]/g)) for (const v of m[1]!.split(';')) { const mm = /^X(\d+)$/.exec(sub(v.trim())); if (mm) gone.add(Number(mm[1])) }
  const width = Math.max(0, ...[...ari!.funs.values()])
  const kept = Array.from({length: width}, (_, i) => i).filter(i => !gone.has(i))
  koat.eliminated = [...gone].sort((a, b) => a - b)
  const blocks = o.split(/\nMPRF for transition /).slice(1)
  for (const b of blocks) {
    const head = /^(\S+): (\S+?)\(.*? of depth (\d+):/s.exec(b)
    if (!head) continue
    const ranks: KRank['ranks'] = {}
    const body = b.slice(b.indexOf('MPRF:'))
    for (const m of body.matchAll(/•\s*(\S+):\s*\[([^\]]*)\]/g)) {
      const e = sub(m[2]!.split(',')[0]!.trim())
      // a linear term over X_i: terms like 2⋅X0, -X1, 20, 1+X0
      const coefs: Record<number, number> = {}
      let k = 0
      for (const t of e.replace(/\s+/g, '').replace(/-/g, '+-').split('+').filter(Boolean)) {
        const mm = /^(-?)(\d*)(?:[⋅*]?X(\d+))?$/.exec(t)
        if (!mm) { k = NaN; break }
        const c = (mm[1] ? -1 : 1) * (mm[2] ? Number(mm[2]) : 1)
        if (mm[3] !== undefined) { const at = kept[Number(mm[3])] ?? -1; coefs[at] = (coefs[at] ?? 0) + c } else k += c
      }
      ranks[m[1]!] = {coefs, k}
    }
    koat.ranks.push({transition: head[1]!, from: head[2]!, depth: Number(head[3]), ranks})
  }
}
out.koat = {answer: koat.answer, seconds: koat.seconds, eliminated: koat.eliminated, mprfs: koat.ranks.length, maxDepth: Math.max(0, ...koat.ranks.map(r => r.depth))}
say({stage: 'koat', ...out.koat as object})

// --- the rules as Z3 text, each rule's variables renamed apart -------------------------------------------------------------
const stripExists = (s: ASx, bound: string[]): ASx => {
  if (typeof s === 'string') return s
  if (s[0] === 'exists') { for (const b of s[1] as ASx[][]) bound.push(b[0] as string); return stripExists(s[2]!, bound) }
  return s.map(x => stripExists(x, bound))
}
const rules = A.rules.map((r, j) => {
  const ex: string[] = []
  const guard = stripExists(r.guard, ex)
  const {lhs, others} = ruleVars(r)
  const m = new Map([...lhs, ...others, ...ex].map(v => [v, `r${j}!${v}`]))
  const ren = (s: ASx): Sx => (typeof s === 'string' ? m.get(s) ?? s : s.map(ren))
  return {
    j, from: r.from, to: r.to, decls: [...new Set(m.values())].map(v => `(declare-const ${sym(v)} Int)`),
    lhs: r.lhs.map(a => show(ren(a))), rhs: r.rhs.map(a => show(ren(a))), guard: show(ren(guard)),
    free: others.filter(v => !ex.includes(v) || true).map(v => sym(m.get(v)!)),
  }
})
const declText = rules.flatMap(r => r.decls).join('\n')
const arity = (l: string) => A.funs.get(l)!
const lit = (v: bigint) => (v < 0n ? `(- ${-v})` : `${v}`)

const varsOf = (s: ASx, o = new Set<string>()): Set<string> => { if (typeof s === 'string') { if (isVar(s)) o.add(s) } else s.forEach((x, i) => (i === 0 && typeof x === 'string' ? undefined : varsOf(x, o))); return o }
function columnsOf(comp: Set<string>, ruleIdx: number[]): Map<string, number[]> {
  const rel = new Map([...comp].map(l => [l, new Set<number>()]))
  // per rule: its guard's conjuncts split into definitions (v = e, v a variable the left side doesn't bind, defined
  // once: an update written as an equation) and conditions (the rest: what the guard reads)
  const flow = ruleIdx.map(j => {
    const r = A.rules[j]!, lhsVars = new Set(r.lhs.filter(a => typeof a === 'string' && isVar(a)) as string[])
    const cs: ASx[] = typeof r.guard !== 'string' && r.guard[0] === 'and' ? r.guard.slice(1) : [r.guard]
    const defs = new Map<string, Set<string>>(), conds: ASx[] = [], targets = new Map<string, number>()
    for (const c of cs) if (Array.isArray(c) && c[0] === '=' && c.length === 3) for (const side of [c[1]!, c[2]!]) if (typeof side === 'string' && isVar(side) && !lhsVars.has(side)) targets.set(side, (targets.get(side) ?? 0) + 1)
    for (const c of cs) {
      if (Array.isArray(c) && c[0] === '=' && c.length === 3) {
        const [x, y] = [c[1]!, c[2]!]
        const v = typeof x === 'string' && isVar(x) && !lhsVars.has(x) && targets.get(x) === 1 && !defs.has(x) ? x : typeof y === 'string' && isVar(y) && !lhsVars.has(y) && targets.get(y) === 1 && !defs.has(y) ? y : undefined
        if (v) { defs.set(v, varsOf(v === x ? y : x)); continue }
      }
      conds.push(c)
    }
    const read = new Set<string>()
    for (const c of conds) varsOf(c, read)
    return {r, defs, read}
  })
  const need = (f: typeof flow[number], vs: Iterable<string>, acc = new Set<string>()): Set<string> => {
    for (const v of vs) { if (acc.has(v)) continue; acc.add(v); const d = f.defs.get(v); if (d) need(f, d, acc) }
    return acc
  }
  const mark = (f: typeof flow[number], vs: Set<string>) => {
    let changed = false
    f.r.lhs.forEach((a, k) => { if (!rel.get(f.r.from)!.has(k) && (!(typeof a === 'string' && isVar(a)) || [...varsOf(a)].some(v => vs.has(v)))) { rel.get(f.r.from)!.add(k); changed = true } })
    return changed
  }
  // what the conditions read, through the definitions; then closed under the updates (a position whose value flows
  // into a relevant position's new value)
  for (const f of flow) mark(f, need(f, f.read))
  for (let changed = true; changed;) {
    changed = false
    for (const f of flow) {
      const vs = new Set<string>()
      f.r.rhs.forEach((a, k) => { if (rel.get(f.r.to)!.has(k)) varsOf(a, vs) })
      if (mark(f, need(f, vs))) changed = true
    }
  }
  return new Map([...rel].map(([l, s]) => [l, [...s].sort((a, b) => a - b)]))
}

// --- sampling ------------------------------------------------------------------------------------------------------------
type Turn = {rule: number, pre: bigint[], post: bigint[]}
const turns: Turn[][] = rules.map(() => [])
const states = new Map<string, Map<string, bigint[]>>([...A.funs.keys()].map(l => [l, new Map()]))
let rx = 23
const rand = (k: number) => { rx = (rx * 1103515245 + 12345) % 2 ** 31; return Math.floor(rx / 2 ** 31 * k) }
const S = new Z3(1000)
S.send(declText)
let steps = 0, unknown = 0, trials = 0
if (sampler === 'z3' || sampler === 'z3+box') {
  await S.check()
  const until = performance.now() + sampleMs
  const record = (l: string, v: bigint[]) => { const m = states.get(l)!; if (m.size < 3000) m.set(v.join(','), v) }
  while (performance.now() < until && performance.now() - T0 < deadline / 2) {
    trials++
    const bound = 1 << Math.min(12, 1 + Math.floor(trials / 3))
    let loc = A.entry, vals = Array.from({length: arity(loc)}, () => BigInt(rand(2 * bound + 1) - bound))
    record(loc, vals)
    for (let d = 0; d < 400 && performance.now() < until; d++) {
      const choices = rules.filter(r => r.from === loc)
      if (!choices.length) break
      let next: {r: typeof rules[number], post: bigint[]} | undefined
      for (let tries = 0; tries < 6 && !next; tries++) {
        const r = choices[rand(choices.length)]!
        const parts = ['(push 1)', ...r.lhs.map((a, k) => `(assert (= ${a} ${lit(vals[k]!)}))`), `(assert ${r.guard})`]
        if (tries < 4) for (const f of r.free) if (rand(2)) { const pool = [0n, 1n, -1n, ...vals, ...vals.map(v => v + 1n), ...vals.map(v => v - 1n), BigInt(rand(2 * bound + 1) - bound)]; parts.push(`(assert (= ${f} ${lit(pool[rand(pool.length)]!)}))`) }
        S.send(parts.join('\n'))
        const res = await S.check()
        steps++
        if (res === 'sat') next = {r, post: (await getValues(S, r.rhs)) as bigint[]}
        if (res === 'unknown') unknown++
        S.send('(pop 1)')
      }
      if (!next) break
      const ts = turns[next.r.j]!
      if (ts.length < 2000) ts.push({rule: next.r.j, pre: vals, post: next.post}); else ts[rand(2000)] = {rule: next.r.j, pre: vals, post: next.post}
      loc = next.r.to; vals = next.post
      record(loc, vals)
    }
  }
}
S.kill()
// Box sampling (--sampler box; z3+box: only the rules the runs never took): per rule, every point of a box of values for the state and the rule's free values (each
// in −B..B, B the largest with (2B+1)^d within --box-points; the values its equations define computed from the
// others), the guard as a word circuit on --target (gpu: Handwired's WGSL on Dawn; cpu: Handwired's CPU loop runner, the
// twin); each point it keeps checked again exactly (ari.ts's evaluator, BigInt) before it becomes a turn. --twin runs
// the CPU twin beside the GPU and counts the documents whose masks differ.
if (sampler === 'box' || sampler === 'z3+box') {
  const g = await import('./gpu.ts')
  const tSetup = performance.now()
  const target = boxTarget === 'gpu' ? await g.gpuTarget() : {kind: 'cpu' as const}
  const budget = Number(opt('--box-points', String(1 << 22)))
  const relevantAll = columnsOf(new Set(A.funs.keys()), A.rules.map((_, j) => j))
  const stats: Record<string, unknown>[] = []
  out.boxTarget = {kind: target.kind, setupMs: Math.round(performance.now() - tSetup), adapter: target.kind === 'gpu' ? target.adapter : undefined}
  for (const [j, r] of A.rules.entries()) {
    // z3+box: the box only for the rules the runs never took; no box past 40% of the deadline
    if (sampler === 'z3+box' && turns[j]!.length) continue
    if (performance.now() - T0 > deadline * 0.4) { stats.push({rule: j, skipped: 'deadline'}); continue }
    const {others} = ruleVars(r)
    const cs: ASx[] = typeof r.guard !== 'string' && r.guard[0] === 'and' ? r.guard.slice(1) : [r.guard]
    // positions: a variable's first occurrence names the value; anything else a fresh name and an equation. Only the
    // positions the program reads (relevant: what some guard reads, closed under the updates, over every rule) are
    // enumerated; the others are 0, and so is a free value nothing relevant reads
    const enumerated: string[] = [], extra: ASx[] = [], rel = relevantAll.get(r.from) ?? []
    const zero: [string, ASx][] = []
    r.lhs.forEach((a, k) => {
      if (!rel.includes(k)) { if (typeof a === 'string' && isVar(a) && !zero.some(([v]) => v === a) && !enumerated.includes(a)) zero.push([a, '0']); return }
      if (typeof a === 'string' && isVar(a) && !enumerated.includes(a)) enumerated.push(a); else { enumerated.push(`@${k}`); extra.push(['=', a, `@${k}`]) }
    })
    const known = new Set([...enumerated, ...zero.map(([v]) => v)]), defined: [string, ASx][] = [...zero]
    for (let changed = true; changed;) {
      changed = false
      for (const c of cs) {
        if (!(Array.isArray(c) && c[0] === '=' && c.length === 3)) continue
        for (const [x, y] of [[c[1]!, c[2]!], [c[2]!, c[1]!]] as [ASx, ASx][]) {
          if (typeof x === 'string' && others.includes(x) && !known.has(x) && [...varsOf(y)].every(v => known.has(v))) { defined.push([x, y]); known.add(x); changed = true; break }
        }
      }
    }
    // a free value is enumerated when a condition of the guard reads it or a relevant new value does (through the
    // definitions); else it is 0
    const defMap = new Map(defined), need = new Set<string>()
    const pull = (vs: Iterable<string>) => { for (const v of vs) { if (need.has(v)) continue; need.add(v); const e = defMap.get(v); if (e) pull(varsOf(e)) } }
    for (const c of cs) { const isDef = Array.isArray(c) && c[0] === '=' && c.length === 3 && defined.some(([v, e]) => (c[1] === v && c[2] === e) || (c[2] === v && c[1] === e)); if (!isDef) pull(varsOf(c)) }
    const relTo = relevantAll.get(r.to) ?? []
    r.rhs.forEach((a, k) => { if (relTo.includes(k)) pull(varsOf(a)) })
    for (const v of others) if (!known.has(v)) { if (need.has(v)) enumerated.push(v); else defined.unshift([v, '0']); known.add(v) }
    const d = enumerated.length
    let B = 0
    while ((2 * (B + 1) + 1) ** d <= budget) B++
    const st: Record<string, unknown> = {rule: j, d, B}
    stats.push(st)
    if (B === 0) { st.skipped = 'too many values for the box'; continue }
    const points = (2 * B + 1) ** d, guard: ASx = ['and', r.guard, ...extra]
    let prog
    try { prog = g.boxProgram(enumerated, defined as never, guard as never, B) } catch (e) { if (e instanceof g.NoWords) { st.skipped = e.message; continue } throw e }
    const docs = Math.ceil(points / 32)
    const t1 = performance.now(), run = await g.runnerOf(target, prog.loop, docs, 1)
    st.compileMs = Math.round(performance.now() - t1)
    const t2 = performance.now(), masks = await run.run(prog.fill(0, points), docs)
    st.runMs = Math.round(performance.now() - t2); st.points = points
    run.destroy()
    if (twin && target.kind === 'gpu') {
      const t3 = performance.now(), cr = await g.runnerOf({kind: 'cpu'}, prog.loop, docs, 1), cm = await cr.run(prog.fill(0, points), docs)
      st.twinMs = Math.round(performance.now() - t3)
      let diff = 0
      for (let i = 0; i < docs; i++) if (masks[i] !== cm[i]) diff++
      st.twinDiffDocs = diff
    }
    // the kept points, checked exactly; a reservoir of 2,000 turns
    let hits = 0, exactFalse = 0, seenHits = 0
    const ts = turns[j]!
    for (let i = 0; i < docs; i++) {
      const m = masks[i]!
      if (!m) continue
      for (let q = 0; q < 32; q++) {
        if (!((m >>> q) & 1)) continue
        hits++
        const vals = prog.decode(i * 32 + q), env = new Map<string, bigint>(enumerated.map((v, k) => [v, BigInt(vals[k]!)]))
        try { for (const [v, e] of defined) env.set(v, evalInt(e, env)) } catch { exactFalse++; continue }
        let ok = false
        try { ok = evalBool(guard, env) } catch { ok = false }
        if (!ok) { exactFalse++; continue }
        const pre = r.lhs.map(a => evalInt(a, env)), post = r.rhs.map(a => evalInt(a, env))
        seenHits++
        const t = {rule: j, pre, post}
        if (ts.length < 2000) ts.push(t); else { const at = rand(seenHits); if (at < 2000) ts[at] = t }
      }
    }
    st.hits = hits; st.exactFalse = exactFalse
    for (const t of ts) { const a = states.get(r.from)!, b = states.get(r.to)!; if (a.size < 3000) a.set(t.pre.join(','), t.pre); if (b.size < 3000) b.set(t.post.join(','), t.post) }
  }
  out.box = stats
}
out.sample = {ms: ms(), trials, steps, unknown, turns: turns.reduce((a, t) => a + t.length, 0), rulesSampled: turns.filter(t => t.length).length, rules: rules.length}
say({stage: 'sample', ...out.sample as object})

// --- components and their columns -----------------------------------------------------------------------------------------
const locs = [...A.funs.keys()], succ = new Map(locs.map(l => [l, new Set<string>()]))
for (const r of A.rules) succ.get(r.from)!.add(r.to)
const sccs: string[][] = []
{
  const index = new Map<string, number>(), low = new Map<string, number>(), on = new Set<string>(), stack: string[] = []
  let i = 0
  const visit = (v: string) => {
    index.set(v, i); low.set(v, i); i++; stack.push(v); on.add(v)
    for (const w of succ.get(v)!) { if (!index.has(w)) { visit(w); low.set(v, Math.min(low.get(v)!, low.get(w)!)) } else if (on.has(w)) low.set(v, Math.min(low.get(v)!, index.get(w)!)) }
    if (low.get(v) === index.get(v)) { const c: string[] = []; let w; do { w = stack.pop()!; on.delete(w); c.push(w) } while (w !== v); sccs.push(c) }
  }
  for (const l of locs) if (!index.has(l)) visit(l)
}
// --- invariants: Q1 + Q2 per location over the sampled states, Houdini by Z3 over every rule --------------------------------
const Zc = new Z3(2000)
Zc.send(declText)
const inv = new Map<string, string[]>()  // location → relations over (p!0 ...)
const P = (k: number) => sym(`p!${k}`)
const linText = (l: Lin, terms: ReturnType<typeof grammar>) => `(${l.op} (+ ${l.coefs.map(([c, x]) => `(* ${lit(x)} ${smtTerm(terms[c]!, n => P(Number(n.slice(1))))})`).join(' ')} ${lit(l.k)}) 0)`
const tInv = performance.now()
{
  const cand = new Map<string, string[]>()
  for (const l of locs) {
    const n = arity(l), names = Array.from({length: n}, (_, k) => `x${k}`)
    const rows: Row[] = [...states.get(l)!.values()].map(v => Object.fromEntries(v.map((x, k) => [`x${k}`, x])))
    if (l === A.entry) { cand.set(l, []); continue }  // the entry: any values
    if (!rows.length) { cand.set(l, ['false']); continue }
    const terms = grammar(names, [], {upTo: 2, caps: {pairs: 30}})
    const t = observe(terms, rows), base = terms.map((_, i) => i).filter(i => terms[i]!.k === 'var')
    cand.set(l, [...equalities(t, base), ...boundRels(bounds(t))].map(x => linText(x, terms)))
  }
  const defs: string[] = []
  for (const [l, cs] of cand) cs.forEach((c, k) => defs.push(`(define-fun ${sym(`I!${l}!${k}`)} (${Array.from({length: arity(l)}, (_, q) => `(${P(q)} Int)`).join(' ')}) Bool ${c})`))
  Zc.send(defs.join('\n'))
  const alive = new Map([...cand].map(([l, cs]) => [l, new Set(cs.map((_, k) => k))]))
  const at = (l: string, k: number, as: string[]) => (as.length ? `(${sym(`I!${l}!${k}`)} ${as.join(' ')})` : sym(`I!${l}!${k}`))
  const conj = (l: string, as: string[]) => `(and true ${[...alive.get(l)!].map(k => at(l, k, as)).join(' ')})`
  let over = false
  for (let changed = true; changed && !over;) {
    changed = false
    for (const r of rules) {
      for (;;) {
        if (performance.now() - T0 > deadline * 0.6) { over = true; break }
        const hs = [...alive.get(r.to)!]
        if (!hs.length) break
        Zc.send(`(push 1)\n(assert ${conj(r.from, r.lhs)})\n(assert ${r.guard})\n(assert (not ${conj(r.to, r.rhs)}))`)
        const res = await Zc.check()
        if (res === 'unsat') { Zc.send('(pop 1)'); break }
        if (res === 'sat') { const v = await getValues(Zc, hs.map(k => at(r.to, k, r.rhs))); Zc.send('(pop 1)'); hs.forEach((k, i) => { if (v[i] === false) alive.get(r.to)!.delete(k) }); changed = true; continue }
        Zc.send('(pop 1)'); alive.get(r.to)!.clear(); changed = true; break
      }
      if (over) break
    }
  }
  for (const [l, s] of alive) inv.set(l, over ? [] : [...s].map(k => at(l, k, Array.from({length: arity(l)}, (_, q) => P(q)))))
  out.invariants = {ms: Math.round(performance.now() - tInv), candidates: [...cand.values()].reduce((a, c) => a + c.length, 0), kept: over ? 0 : [...alive.values()].reduce((a, s) => a + s.size, 0), over}
  say({stage: 'invariants', ...out.invariants as object})
}
const invAt = (l: string, as: string[]) => { const xs = inv.get(l) ?? []; if (!xs.length) return 'true'; return `(let (${as.map((a, q) => `(${P(q)} ${a})`).join(' ')}) (and true ${xs.join(' ')}))` }

// --- Q3, KoAT2's way ---------------------------------------------------------------------------------------------------------
type Rk = Ranking
const rText = (rk: Rk, cols: Map<string, number[]>, l: string, as: string[]) => {
  const c = rk.coefs.get(l)!, ps = cols.get(l)!.map((pos, i) => (c[i] ? `(* ${lit(c[i]!)} ${as[pos]})` : '')).filter(Boolean)
  return `(+ ${lit(rk.k.get(l)!)} ${ps.join(' ')})`
}
// the check of a rank's condition on one rule; where Z3 finds a turn that breaks it, that turn (a counterexample
// row: the verifier's model of the rule, the table's next row)
let cex: Turn | undefined
async function valid(rule: typeof rules[number], body: string, withInv: boolean): Promise<boolean> {
  if (performance.now() - T0 > deadline) { timedOut = true; return false }
  Zc.send(`(push 1)\n(assert ${rule.guard})\n${withInv ? `(assert ${invAt(rule.from, rule.lhs)})` : ''}\n(assert (not ${body}))`)
  const r = await Zc.check()
  cex = undefined
  if (r === 'sat' && withInv) { try { const v = (await getValues(Zc, [...rule.lhs, ...rule.rhs])) as bigint[]; cex = {rule: rule.j, pre: v.slice(0, rule.lhs.length), post: v.slice(rule.lhs.length)} } catch { /* a value we can't read */ } }
  Zc.send('(pop 1)')
  return r === 'unsat'
}
async function minOf(rule: typeof rules[number], e: string): Promise<bigint | undefined> {
  if (performance.now() - T0 > deadline) return undefined
  const o = await Zc.ask(`(push 1)\n(assert ${rule.guard})\n(assert ${invAt(rule.from, rule.lhs)})\n(minimize ${e})\n(check-sat)\n(get-objectives)\n(pop 1)`)
  if (!/^sat/m.test(o)) return undefined
  const m = /\(objectives\s*\(\S.*?\s+(\(- \d+\)|-?\d+)\)\s*\)/s.exec(o)
  if (!m) return undefined
  const v = m[1]!
  return v.startsWith('(-') ? -BigInt(v.slice(3, -1)) : BigInt(v)
}
const comps: Record<string, unknown>[] = []
let timedOut = false
let allRanked = true, noTurn = 0
const tRank = performance.now()
for (const c of sccs) {
  const comp = new Set(c), ruleIdx = A.rules.map((r, j) => j).filter(j => comp.has(A.rules[j]!.from) && comp.has(A.rules[j]!.to))
  if (!ruleIdx.length) continue
  const cols = columnsOf(comp, ruleIdx), cl = [...comp], n = Math.max(1, ...cl.map(l => cols.get(l)!.length))
  const proj = (l: string, v: bigint[]) => { const ps = cols.get(l)!; return Array.from({length: n}, (_, i) => (i < ps.length ? v[ps[i]!]! : 0n)) }
  const extra = new Map<number, Turn[]>()
  const rowsOf = (j: number): Pair[] => [...turns[j]!, ...(extra.get(j) ?? [])].map(t => ({from: A.rules[j]!.from, to: A.rules[j]!.to, pre: proj(A.rules[j]!.from, t.pre), post: proj(A.rules[j]!.to, t.post)}))
  const U = new Set(ruleIdx), found: {strict: number[], rank: Record<string, string>, withInv: boolean}[] = []
  const sampled = ruleIdx.filter(j => turns[j]!.length).length
  if (!sampled) noTurn++
  // a rule whose guard no state meets (with the invariants) takes no turn
  for (const j of [...U]) if (await valid(rules[j]!, 'false', true)) U.delete(j)
  let lpCalls = 0, refused = 0, cexRows = 0
  const refusedShown: Record<string, string>[] = []
  for (let progress = true; progress && U.size && performance.now() - T0 < deadline;) {
    progress = false
    for (const t of [...U]) {
      if (!U.has(t) || !turns[t]!.length) continue
      let rk: Ranking | undefined, ok = false, withInv = false
      for (let round = 0; round < 6 && !ok && !timedOut; round++) {
        lpCalls++
        const cands = ranks(rowsOf(t), [...U].filter(u => u !== t).flatMap(rowsOf), cl, n, 12)
        if (!cands.length) break
        let broke: Turn | undefined
        for (const c0 of cands) {
          if (performance.now() - T0 > deadline) { timedOut = true; break }
          // the constants from the rules rather than the samples: per rule u still unbounded, the least value of
          // c_from·x − c_to·x' where u's guard holds (with the invariants, by Z3's optimizer) gives d_from − d_to ≥
          // [u = t] − that; and d_from ≥ −min c_from·x on t; solved as difference constraints. None where a minimum is
          // unbounded (then the samples' constants are kept)
          let r0 = c0
          {
            const zero: Ranking = {...c0, k: new Map(cl.map(l => [l, 0n]))}, li = new Map(cl.map((l, i) => [l, i]))
            const need: {a: bigint[], a0: bigint, b: bigint}[] = []
            let okc = true
            for (const u of [t, ...[...U].filter(u => u !== t)]) {
              const r = rules[u]!, w = await minOf(r, `(- ${rText(zero, cols, r.from, r.lhs)} ${rText(zero, cols, r.to, r.rhs)})`)
              if (w === undefined) { okc = false; break }
              const a: bigint[] = cl.map(() => 0n)
              a[li.get(r.from)!]! += 1n; a[li.get(r.to)!]! -= 1n
              const b = (u === t ? 1n : 0n) - w
              if (r.from === r.to) { if (b > 0n) { okc = false; break } continue }
              need.push({a, a0: 0n, b})
            }
            if (okc) {
              const r = rules[t]!, lo = await minOf(r, rText(zero, cols, r.from, r.lhs))
              if (lo === undefined) okc = false
              else { const a: bigint[] = cl.map(() => 0n); a[li.get(r.from)!] = 1n; need.push({a, a0: 0n, b: -lo}) }
            }
            const ds = okc ? differences(need, cl.length) : undefined
            if (ds) r0 = {...c0, k: new Map(cl.map((l, i) => [l, ds[i]!]))}
          }
          const strictBody = (u: number) => { const r = rules[u]!; return `(and (>= (- ${rText(r0, cols, r.from, r.lhs)} ${rText(r0, cols, r.to, r.rhs)}) 1) (>= ${rText(r0, cols, r.from, r.lhs)} 0))` }
          const weakBody = (u: number) => { const r = rules[u]!; return `(>= (- ${rText(r0, cols, r.from, r.lhs)} ${rText(r0, cols, r.to, r.rhs)}) 0)` }
          for (const wi of [false, true]) {
            if (!(await valid(rules[t]!, strictBody(t), wi))) { broke = cex ?? broke; continue }
            let all = true
            for (const u of U) if (u !== t && !(await valid(rules[u]!, weakBody(u), wi))) { all = false; broke = cex ?? broke; break }
            if (all) { ok = true; withInv = wi; break }
          }
          if (ok) { rk = r0; break }
          refused++
          if (refusedShown.length < 3) refusedShown.push(Object.fromEntries(cl.map(l => [l, `${r0.coefs.get(l)!.map((x, i) => (x ? `${x}·x${cols.get(l)![i]}` : '')).filter(Boolean).join(' + ') || '0'} + ${r0.k.get(l)}`])))
        }
        if (ok || !broke) break
        // the last counterexample becomes a row, and the table is asked again
        cexRows++
        extra.set(broke.rule, [...(extra.get(broke.rule) ?? []), broke])
      }
      if (!ok || !rk) continue
      const strictBody = (u: number) => { const r = rules[u]!; return `(and (>= (- ${rText(rk!, cols, r.from, r.lhs)} ${rText(rk!, cols, r.to, r.rhs)}) 1) (>= ${rText(rk!, cols, r.from, r.lhs)} 0))` }
      const strict = [t]
      for (const u of U) if (u !== t && (await valid(rules[u]!, strictBody(u), withInv))) strict.push(u)
      for (const u of strict) U.delete(u)
      const shown: Record<string, string> = {}
      for (const l of cl) shown[l] = `${rk.coefs.get(l)!.map((x, i) => (x ? `${x}·x${cols.get(l)![i]}` : '')).filter(Boolean).join(' + ') || '0'} + ${rk.k.get(l)}`
      found.push({strict, rank: shown, withInv})
      // against KoAT2's: a rank of KoAT2's whose terms at each of its locations are this one's up to a positive factor
      ;(found.at(-1) as Record<string, unknown>).raw = Object.fromEntries(cl.map(l => [l, {coefs: Object.fromEntries(rk.coefs.get(l)!.map((x, i) => [cols.get(l)![i]!, Number(x)]).filter(([, x]) => x)), k: Number(rk.k.get(l))}]))
      progress = true
    }
  }
  const ranked = U.size === 0
  if (!ranked) allRanked = false
  // KoAT2's ranks at this component's locations: their positions within the columns? proportional to one found here?
  const kr = koat.ranks.filter(k => Object.keys(k.ranks).some(l => cl.some(x => koatName(x) === l)))
  let within = 0, same = 0
  for (const k of kr) {
    const inCols = Object.entries(k.ranks).every(([l, r]) => { const x = cl.find(y => koatName(y) === l); return !x || Object.keys(r.coefs).every(p => r.coefs[Number(p)] === 0 || cols.get(x)!.includes(Number(p))) })
    if (inCols) within++
    const prop = found.some(f => Object.entries(k.ranks).every(([l, r]) => {
      const x = cl.find(y => koatName(y) === l)
      if (!x) return true
      const ours = ((f as Record<string, unknown>).raw as Record<string, {coefs: Record<string, number>}>)[x]!.coefs
      const ks = new Set([...Object.keys(r.coefs).filter(p => r.coefs[Number(p)] !== 0), ...Object.keys(ours)])
      let ratio: number | undefined
      for (const p of ks) { const a = r.coefs[Number(p)] ?? 0, b = ours[p] ?? 0; if (!a || !b) return false; const q = b / a; if (q <= 0 || (ratio !== undefined && Math.abs(q - ratio) > 1e-9)) return false; ratio = q }
      return true
    }))
    if (prop) same++
  }
  comps.push({locations: cl.length, rules: ruleIdx.length, sampled, columns: Object.fromEntries(cl.map(l => [l, `${cols.get(l)!.length}/${arity(l)}`])), ranked, left: U.size, lpCalls, refused, cexRows, refusedShown, found: found.map(f => ({strict: f.strict.length, rank: f.rank, withInv: f.withInv})), koat: {mprfs: kr.length, withinColumns: within, sameAsOurs: same}, colsAt: Object.fromEntries(cl.map(l => [l, cols.get(l)])), koatRanks: kr, ours: found.map(f => (f as Record<string, unknown>).raw)})
}
out.rank = {ms: Math.round(performance.now() - tRank), components: comps.length, noTurn, timedOut}
out.components = comps
out.answer = allRanked ? 'terminates' : 'unknown'
Zc.kill()
out.z3 = {calls: Zc.calls, ms: Math.round(Zc.ms)}
done()
