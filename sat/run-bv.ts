// The k = 31 and k = 64 enumeration laws of lean/ProbeBv.lean and lean/ProbeBv64.lean, without Lean: bit-blasted here,
// the negation refuted by solver.ts, the DRUP proof checked by check.ts. The false variant (ProbeBvFalse.lean) gets a
// model, decoded to w and re-checked on plain bigints.
import {checkModel, checkProof} from './check.ts'
import {Circuit, decode} from './cnf.ts'
import {solve} from './solver.ts'

const consts = {31: [0x55555555n, 0x09249249n], 64: [0x5555555555555555n, 0x1249249249249249n]} as const

// The law's hypotheses and its conclusion, as literals; `claim` is the top atom being off (true law) or on (false one).
function law(width: 31 | 64, claimOff: boolean) {
  const g = new Circuit()
  const [E, T] = consts[width]
  const w = g.input(width), e = g.const(width, E), t = g.const(width, T)
  const one = g.const(width, 1n), zero = g.const(width, 0n)
  const topBit = g.shl(one, width - 1)
  const reach = g.isZero(g.band(g.band(g.shr(w, 1), e), g.bnot(w)))
  const c = g.band(g.band(g.band(w, g.shr(w, 1)), g.bnot(g.shr(w, 2))), t)
  const topOff = g.isZero(g.band(w, topBit))
  const c2 = g.bor(g.band(c, g.bnot(one)), g.band(g.band(c, one), g.bite(topOff, zero, one)))
  const hyps = g.every([reach, -g.isZero(c), g.isZero(c2)])
  // The negation of hyps → conclusion.
  g.assert(hyps)
  g.assert(claimOff ? -topOff : topOff)
  return {g, w}
}

// The same law on bigints, for re-checking a model.
function holds(width: 31 | 64, w: bigint, claimOff: boolean) {
  const mask = (1n << BigInt(width)) - 1n, [e, t] = consts[width]
  const not = (y: bigint) => ~y & mask
  const top = 1n << BigInt(width - 1)
  const reach = ((w >> 1n) & e & not(w)) === 0n
  const c = w & (w >> 1n) & not(w >> 2n) & t
  const c2 = (c & not(1n)) | (c & 1n & ((w & top) === 0n ? 0n : 1n))
  const off = (w & top) === 0n
  return !(reach && c !== 0n && c2 === 0n) || (claimOff ? off : !off)
}

const rows: string[] = []
for (const [width, claimOff, what] of [[31, true, 'k=31 law'], [64, true, 'k=64 law'], [31, false, 'k=31 false variant'], [64, false, 'k=64 false variant']] as const) {
  const {g, w} = law(width, claimOff)
  const t0 = performance.now()
  const r = solve(g.vars, g.clauses)
  const t1 = performance.now()
  const ok = r.kind === 'sat' ? checkModel(g.clauses, r.model) : checkProof(g.clauses, r.proof)
  const t2 = performance.now()
  const detail = r.kind === 'unsat' ? `PROVEN, DRUP ${r.proof.length} clauses (${r.proof.reduce((s, c) => s + c.length, 0)} literals)`
    : (() => { const value = decode(r.model, w); return `REFUTED, w = ${value} (bigint re-check: law ${holds(width, value, claimOff) ? 'holds?!' : 'fails'})` })()
  rows.push(`| ${what} | ${g.vars} | ${g.clauses.length} | ${(t1 - t0).toFixed(1)} ms | ${(t2 - t1).toFixed(1)} ms ${ok ? 'checked' : 'REJECTED'} | ${detail} |`)
}
console.log('| law | vars | clauses | solve | check | verdict |\n| --- | --- | --- | --- | --- | --- |\n' + rows.join('\n'))

// The laws above fall to unit propagation alone (an empty-clause proof). Harder ones, where the solver must search:
// adder identities, stated as "no a, b, c breaks them".
const harder: [string, (g: Circuit) => number][] = [
  ['a + b = b + a, 32 bits', g => { const a = g.input(32), b = g.input(32); return -g.eq(g.add(a, b), g.add(b, a)) }],
  ['a + a = a << 1, 32 bits', g => { const a = g.input(32); return -g.eq(g.add(a, a), g.shl(a, 1)) }],
  ['(a + b) + c = a + (b + c), 8 bits', g => { const [a, b, c] = [g.input(8), g.input(8), g.input(8)]; return -g.eq(g.add(g.add(a, b), c), g.add(a, g.add(b, c))) }],
  ['(a + b) + c = a + (b + c), 12 bits', g => { const [a, b, c] = [g.input(12), g.input(12), g.input(12)]; return -g.eq(g.add(g.add(a, b), c), g.add(a, g.add(b, c))) }],
  ['a < b and b < c imply a < c, 32 bits', g => { const [a, b, c] = [g.input(32), g.input(32), g.input(32)]; return g.every([g.ult(a, b), g.ult(b, c), -g.ult(a, c)]) }],
  ['a <= a + b (false: overflow), 16 bits', g => { const a = g.input(16), b = g.input(16); return -g.ule(a, g.add(a, b)) }],
]
const more: string[] = []
for (const [what, build] of harder) {
  const g = new Circuit()
  g.assert(build(g))
  const t0 = performance.now()
  const r = solve(g.vars, g.clauses)
  const t1 = performance.now()
  const ok = r.kind === 'sat' ? checkModel(g.clauses, r.model) : checkProof(g.clauses, r.proof)
  const t2 = performance.now()
  more.push(`| ${what} | ${g.vars} | ${g.clauses.length} | ${(t1 - t0).toFixed(1)} ms | ${(t2 - t1).toFixed(1)} ms ${ok ? 'checked' : 'REJECTED'} | ${r.kind === 'unsat' ? `PROVEN, DRUP ${r.proof.length} clauses` : 'REFUTED (a model)'} |`)
}
console.log('\n| identity | vars | clauses | solve | check | verdict |\n| --- | --- | --- | --- | --- | --- |\n' + more.join('\n'))
