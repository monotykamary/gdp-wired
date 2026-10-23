// Conformance: one generator of random terms and conditions over every operation (the lists below must name every op of
// E and C, or this file doesn't type-check), and every consumer of terms held to the reference evaluator (evalE, evalC):
//   - the interpreter and the generated JavaScript, stepping a machine whose step computes the term;
//   - the kernel and its prover, on the term with every variable and map cell fixed: the kernel must accept a proof
//     that the term equals its value, never one that it differs (a model of the negation would be a disagreement), and
//     never a proof of something with a model;
//   - the GPU search's u32 JavaScript twin (research/search/compile.ts);
//   - the old symbolic prover's cases (conditionCases), where it applies;
//   - and the Lean printer, through lean-kernel/conformance.ts, which writes the same cases for Lean's evalE.
// Each consumer either agrees or refuses with an error; undefined, NaN or a silent different answer fails.
import {expect, test} from 'bun:test'
import {type C, type E, compileFunction, conditionCases, interpret, loadJs} from './machine.ts'
import {type Case, C_OPS, CELLS, E_OPS, QC_OPS, QE_OPS, VARS, inlineC, inlineE, kindAnswer, kindCases, kindReference, machineOf, qcoverage, qgoals, qmachineOf, qreference, qtampered, randomCase, randomQCase, recurCases, recurReference, reference, seen, stateOf} from './conformance.ts'
import {type Loop, type Recur, check, checkQTree, checkRecur, recurGoal} from '../kernel/kernel.ts'
import {recurLean} from '../lean-kernel/emit.ts'
import {growQ} from '../kernel/qprove.ts'
import {q, qeq} from './q.ts'
import {evalQC, interpretQ, loadQJs} from './rationals.ts'
import {grow} from '../kernel/prove.ts'
import {expressions} from '../research/search/compile.ts'

const scale = Number(process.env.FUZZ_SCALE ?? 1)
let seed2 = Number(process.env.FUZZ_SEED ?? 777) + 1
const rand = (k: number) => { seed2 = (seed2 * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed2 / 2 ** 31 * k) }

const hasProd = (t: E | C): boolean => JSON.stringify(t).includes('"op":"prod"')
const n = (value: number): E => ({op: 'const', value})
const fixed = (k: Case): C[] => [
  ...VARS.map(v => ({op: '=', a: {op: 'var', name: v}, b: n(k.input[v]!)}) as C),
  ...k.cells.map((v, i) => ({op: '=', a: {op: 'get', map: 'M', key: n(i)}, b: n(v)}) as C),
]

test('every consumer of terms agrees with the reference evaluator, or refuses', () => {
  let cases = 0, kernelProved = 0, kernelUnknown = 0, u32 = 0, symbolic = 0
  for (let trial = 0; trial < 500 * scale; trial++) {
    const k = randomCase(1 + rand(3))
    const ref = reference(k)
    expect(Number.isSafeInteger(ref.value)).toBe(true)
    const m = machineOf(k)

    // The interpreter and the generated JavaScript.
    const out = interpret(m).step({}, stateOf(k), k.input)
    expect(out.scalars.out).toBe(ref.value)
    expect(out.scalars.ok).toBe(ref.holds ? 1 : 0)
    const js = loadJs(m).step({}, stateOf(k), k.input)
    expect(js.scalars.out).toBe(ref.value)
    expect(js.scalars.ok).toBe(ref.holds ? 1 : 0)

    // The kernel: with everything fixed, the term equals its value and the condition has its truth.
    const t = inlineE(k.t, k.f), c = inlineC(k.c, k.f), hyps = fixed(k)
    const claims: [string, C][] = [['value', {op: '=', a: t, b: n(ref.value)}], ['truth', ref.holds ? c : {op: 'not', x: c}]]
    for (const [what, claim] of claims) {
      const negated: C = {op: 'not', x: claim}
      if (!hasProd(claim)) {
        // Linear, every variable fixed: always proven, and the kernel accepts the tree.
        const right = grow({name: what, hyps: [...hyps, negated]})
        expect('tree' in right, `${what}: ${'stuck' in right ? right.stuck : ''} ${JSON.stringify(k)}`).toBe(true)
        if ('tree' in right) expect(check({name: what, hyps: [...hyps, negated]}, right.tree)).toBe(true)
        kernelProved++
      } else kernelUnknown++
      // Never a proof of the negation, which has a model (the reference's own values). Products get 200 ms: the prover
      // treats their monomials as free variables, so it may wander; what matters is that it never closes.
      const wrong = grow({name: `not ${what}`, hyps: [...hyps, claim]}, new Map(), {nodes: 0, until: performance.now() + (hasProd(claim) ? 200 : 20_000)})
      if ('tree' in wrong) expect(check({name: `not ${what}`, hyps: [...hyps, claim]}, wrong.tree)).toBe(false)
    }

    // The GPU search's u32 twin, on the same values (all far below 2^32).
    const names = (v: string) => (v === 'f' ? 'f_f' : `i_${v}`)
    const {ex, cx} = expressions(m, 'js', v => names(v), CELLS)
    const fJs = compileFunction<(...xs: unknown[]) => boolean>(['i_a', 'i_b', 'i_c', 'm_M'], `return ${cx(k.f)}`)
    const mArr = [...k.cells]
    const fVal = fJs(k.input.a, k.input.b, k.input.c, mArr)
    const tJs = compileFunction<(...xs: unknown[]) => number>(['i_a', 'i_b', 'i_c', 'm_M', 'f_f'], `return ${ex(k.t)}`)
    const cJs = compileFunction<(...xs: unknown[]) => boolean>(['i_a', 'i_b', 'i_c', 'm_M', 'f_f'], `return ${cx(k.c)}`)
    expect(tJs(k.input.a, k.input.b, k.input.c, mArr, fVal)).toBe(ref.value)
    expect(Boolean(cJs(k.input.a, k.input.b, k.input.c, mArr, fVal))).toBe(ref.holds)
    u32++

    // The old symbolic prover's cases, for conditions without maps or products: true exactly when some case holds.
    if (!JSON.stringify(c).includes('"op":"get"') && !hasProd(c)) {
      const env = k.input
      const holds = (lin: Record<string, number>) => Object.entries(lin).reduce((s, [v, coef]) => s + coef * (v === '1' ? 1 : env[v]!), 0) <= 0
      const some = conditionCases(c, true).some(cs => cs.every(con => holds(con.lin)))
      const none = conditionCases(c, false).some(cs => cs.every(con => holds(con.lin)))
      expect(some).toBe(ref.holds)
      expect(none).toBe(!ref.holds)
      symbolic++
    }
    cases++
  }
  // Every op was exercised.
  for (const op of [...E_OPS, ...C_OPS]) expect(seen[op] ?? 0, op).toBeGreaterThan(20 * scale)
  console.log(`conformance: ${cases} cases (${Object.entries(seen).map(([o, c]) => `${o} ${c}`).join(', ')}); kernel proved ${kernelProved}, unknown ${kernelUnknown} (products); u32 twin ${u32}; symbolic ${symbolic}`)
}, 600_000)

// Nontermination certificates (kernel.ts's checkRecur): every certificate the checker accepts holds on the reference's
// run (the stem replayed by evalE and evalC, then the witnessed turn again and again, each allowed and in the set);
// every one the search found is accepted; every tampered one is refused (the set not closed, not reached, a lasso's cycle
// that doesn't close), and where the set was changed no tree closes it (the prover finds a state of it that leaves it).
// lean-kernel/conformance.ts --nonterm writes the same cases for Lean's checkRecur.
test('nontermination certificates: accepted ones hold on the reference run, tampered ones are refused', () => {
  const counts: Record<string, {n: number, accepted: number}> = {}, found = new Map<Loop, Recur>()
  for (const c of recurCases(Math.round(60 * scale))) {
    // Its Lean text, as lean-kernel/conformance.ts --nonterm writes it: every number an integer (Lean's Int has no
    // fraction), so Lean computes an answer on it rather than refusing to read it.
    if (c.what === 'found') found.set(c.loop, c.recur)
    const text = recurLean('case', c.loop, found.get(c.loop) ?? c.recur).recur(c.recur)
    expect(/\d\.\d|e[+-]?\d|NaN|Infinity/.test(text), `${c.loop.name}: ${c.what}: a number Lean can't read`).toBe(false)
    let ok = false
    try { ok = checkRecur(c.loop, c.recur) } catch { ok = false }
    const at = (counts[c.what] ??= {n: 0, accepted: 0})
    at.n++
    if (ok) at.accepted++
    if (ok) expect(recurReference(c.loop, c.recur), `${c.loop.name}: ${c.what}`).toBe(true)
    if (c.what === 'found') expect(ok, c.loop.name).toBe(true)
    if (c.what !== 'found') expect(ok, `${c.loop.name}: ${c.what}`).toBe(false)
    if (c.what.startsWith('the set not closed') || c.what.startsWith("a lasso's cycle")) expect('tree' in grow(recurGoal(c.loop, c.recur)), `${c.loop.name}: ${c.what}`).toBe(false)
  }
  for (const what of ['found', 'the set not closed: every state', 'the set not reached: a start whose stem ends outside it', 'the set not reached: a stem turn the guard or the assumption refuses', "a lasso's cycle that doesn't close: its set less one state", 'forged: the guard as the set']) expect(counts[what]?.n ?? 0, what).toBeGreaterThan(0)
  console.log(`nontermination: ${Object.entries(counts).map(([w, x]) => `${w} ${x.accepted}/${x.n} accepted`).join('; ')}`)
}, 600_000)

// k-induction certificates (kernel.ts's checkKInduction): every certificate the search finds is accepted and its law
// holds on the reference's runs; the same certificate for another k, a base depth left out, the step's tree for k given
// for k − 1 (a law k-inductive only at k) or inside a certificate for k + 1 are refused; any certificate accepted (the
// law read stricter may still be true) holds on the reference's runs. lean-kernel/conformance.ts --kind writes the same
// cases for KInd.lean's checkKInd.
test('k-induction certificates: found ones accepted and true, tampered ones refused', () => {
  const counts: Record<string, {n: number, accepted: number}> = {}
  for (const c of kindCases(Math.round(30 * scale))) {
    for (const t of [{what: 'found', kl: c.kl, proof: c.proof}, ...c.tampers]) {
      const ok = kindAnswer(c, t), what = t.what.replace(/\d+/g, 'k'), at = (counts[what] ??= {n: 0, accepted: 0})
      at.n++
      if (ok) at.accepted++
      if (ok) expect(kindReference(c.m, t.kl.law), `${c.m.name}: ${t.what}`).toBe(true)
      if (t.what === 'found') expect(ok, c.m.name).toBe(true)
      else if (t.what !== 'the law read stricter') expect(ok, `${c.m.name}: ${t.what}`).toBe(false)
    }
  }
  for (const what of ['found', 'k said to be k', 'the base of depth k left out', 'k-inductive only at k = k: the step\'s tree for k given for k', 'the step\'s tree for k = k in a certificate for k']) expect(counts[what]?.n ?? 0, what).toBeGreaterThan(0)
  console.log(`k-induction: ${Object.entries(counts).map(([w, x]) => `${w} ${x.accepted}/${x.n} accepted`).join('; ')}`)
}, 600_000)

// Rationals: the interpreter and the generated JavaScript against the reference (exact), and the kernel on each case's
// goals: the claim negated, with every variable fixed, is proven, and the tree checks; the claim itself, which the
// case's values satisfy, is never proven (the search ends at a model the reference confirms); each proven tree's
// tampered twins are refused. Lean computes the same answers on these cases (lean-kernel/conformance.ts --rationals).
test('rationals: every consumer of rational terms agrees with the reference; tampered certificates are refused', () => {
  let proven = 0, models = 0, tampered = 0
  for (let trial = 0; trial < 300 * scale; trial++) {
    const k = randomQCase(1 + rand(3)), ref = qreference(k), m = qmachineOf(k), none = {}
    const input = k.env
    for (const run of [interpretQ(m), loadQJs(m)]) {
      const out = run.step(none, {out: q(0), ok: q(0)}, input)
      expect(qeq(out.out!, ref.value)).toBe(true)
      expect(qeq(out.ok!, q(ref.holds ? 1 : 0))).toBe(true)
    }
    const goals = qgoals(k)
    for (const g of goals.proven) {
      const out = growQ(g)
      expect('tree' in out, `${g.name}: ${'stuck' in out ? out.stuck : ''} ${JSON.stringify(k, (_, x) => (typeof x === 'bigint' ? String(x) : x))}`).toBe(true)
      if (!('tree' in out)) continue
      expect(checkQTree(g, out.tree)).toBe(true)
      proven++
      for (const t of qtampered(out.tree)) { expect(checkQTree(g, t.tree), t.what).toBe(false); tampered++ }
    }
    for (const g of goals.models) {
      const out = growQ(g)
      if ('tree' in out) expect(checkQTree(g, out.tree)).toBe(false)
      else {
        expect(out.stuck).toBe('sat')
        const at = Object.fromEntries(VARS.map(x => [x, out.rational?.[x] ?? q(0)]))
        expect(g.hyps.every(h => evalQC(h, at))).toBe(true)
        models++
      }
    }
  }
  expect(qcoverage).toEqual([true, true])
  for (const op of [...QE_OPS, ...QC_OPS]) expect(seen[`q${op}`] ?? 0, op).toBeGreaterThan(0)
  console.log(`rationals: ${proven} goals proven and checked, ${models} models found and confirmed, ${tampered} tampered trees refused`)
})
