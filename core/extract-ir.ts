// The extractor's terms (core/extract.ts): what a step of the code computes, read symbolically from its TypeScript, before
// it is printed as a rule. Numbers are exact integers here (no sort yet: core/extract.ts decides which are naturals),
// conditions are booleans, a choice is one of a string-literal union's values, a key is a map's key (a number or a
// string). Every constructor simplifies what it can decide (constants, one branch), so the printed rule stays near
// the code's own size. Nothing here is trusted: the rule printed from these terms is run against the code itself.
export type N =
  | {op: 'var', name: string}
  | {op: 'const', v: number}
  | {op: 'add' | 'sub' | 'min' | 'max' | 'mul', a: N, b: N}
  | {op: 'neg', a: N}
  | {op: 'mulk', k: number, a: N}
  | {op: 'divk' | 'modk', k: number, a: N}
  | {op: 'ite', c: B, a: N, b: N}
  | {op: 'cell', map: string, key: K, field: string}
export type B =
  | {op: 'const', v: boolean}
  | {op: 'var', name: string}
  | {op: 'cmp', rel: '<' | '<=' | '=', a: N, b: N}
  | {op: 'and' | 'or', xs: B[]}
  | {op: 'not', x: B}
  | {op: 'ite', c: B, a: B, b: B}
  | {op: 'is', l: L, value: string}
  | {op: 'leq', a: L, b: L}
  | {op: 'keq', a: K, b: K}
  | {op: 'cell', map: string, key: K, field: string}
export type L =
  | {op: 'var', name: string, values: string[]}
  | {op: 'lit', value: string, values: string[]}
  | {op: 'ite', c: B, a: L, b: L}
  | {op: 'cell', map: string, key: K, field: string, values: string[]}
// A key: a number, a string input, a string literal, or one of two by a condition.
export type K = {op: 'num', e: N} | {op: 'svar', name: string} | {op: 'slit', value: string} | {op: 'kite', c: B, a: K, b: K}

// Structural keys (memoized: the same object is compared many times while paths merge).
const keys = new WeakMap<object, string>()
export const keyOf = (x: object): string => {
  let k = keys.get(x)
  if (k === undefined) { k = JSON.stringify(x); keys.set(x, k) }
  return k
}
export const same = (a: object, b: object): boolean => a === b || keyOf(a) === keyOf(b)

// --- numbers --------------------------------------------------------------------------------------------------------
export const num = (v: number): N => ({op: 'const', v})
export const nvar = (name: string): N => ({op: 'var', name})
const isC = (e: N): e is {op: 'const', v: number} => e.op === 'const'
export const add = (a: N, b: N): N => (isC(a) && isC(b) ? num(a.v + b.v) : isC(a) && a.v === 0 ? b : isC(b) && b.v === 0 ? a : {op: 'add', a, b})
export const sub = (a: N, b: N): N => (isC(a) && isC(b) ? num(a.v - b.v) : isC(b) && b.v === 0 ? a : same(a, b) ? num(0) : {op: 'sub', a, b})
export const neg = (a: N): N => (isC(a) ? num(-a.v) : a.op === 'neg' ? a.a : {op: 'neg', a})
export const mulk = (k: number, a: N): N => (k === 0 ? num(0) : k === 1 ? a : isC(a) ? num(k * a.v) : {op: 'mulk', k, a})
export const mul = (a: N, b: N): N => (isC(a) ? mulk(a.v, b) : isC(b) ? mulk(b.v, a) : {op: 'mul', a, b})
export const nmin = (a: N, b: N): N => (isC(a) && isC(b) ? num(Math.min(a.v, b.v)) : same(a, b) ? a : {op: 'min', a, b})
export const nmax = (a: N, b: N): N => (isC(a) && isC(b) ? num(Math.max(a.v, b.v)) : same(a, b) ? a : {op: 'max', a, b})
export const divk = (k: number, a: N): N => (k === 1 ? a : isC(a) ? num(Math.floor(a.v / k)) : {op: 'divk', k, a})
export const modk = (k: number, a: N): N => (k === 1 ? num(0) : isC(a) && a.v >= 0 ? num(a.v % k) : {op: 'modk', k, a})
export const nite = (c: B, a: N, b: N): N => (c.op === 'const' ? (c.v ? a : b) : same(a, b) ? a : c.op === 'not' ? nite(c.x, b, a) : {op: 'ite', c, a, b})

// --- conditions -----------------------------------------------------------------------------------------------------
export const T: B = {op: 'const', v: true}
export const F: B = {op: 'const', v: false}
export const bvar = (name: string): B => ({op: 'var', name})
export const cmp = (rel: '<' | '<=' | '=', a: N, b: N): B => {
  if (isC(a) && isC(b)) return rel === '<' ? (a.v < b.v ? T : F) : rel === '<=' ? (a.v <= b.v ? T : F) : a.v === b.v ? T : F
  if (same(a, b)) return rel === '<' ? F : T
  return {op: 'cmp', rel, a, b}
}
export const and = (...xs: B[]): B => {
  const out: B[] = []
  for (const x of xs.flatMap(x => (x.op === 'and' ? x.xs : [x]))) {
    if (x.op === 'const') { if (!x.v) return F; continue }
    if (out.some(y => same(x, y))) continue
    if (out.some(y => (y.op === 'not' && same(y.x, x)) || (x.op === 'not' && same(x.x, y)))) return F
    out.push(x)
  }
  // A choice is one value at a time: two values contradict, and one implies it is none of the others.
  const iss = out.filter((x): x is Extract<B, {op: 'is'}> => x.op === 'is')
  if (iss.some(a => iss.some(b => b.value !== a.value && same(a.l, b.l)))) return F
  const kept = out.filter(x => !(x.op === 'not' && x.x.op === 'is' && iss.some(a => same(a.l, (x.x as Extract<B, {op: 'is'}>).l) && a.value !== (x.x as Extract<B, {op: 'is'}>).value)))
  return kept.length === 0 ? T : kept.length === 1 ? kept[0]! : {op: 'and', xs: kept}
}
export const or = (...xs: B[]): B => {
  const out: B[] = []
  for (const x of xs.flatMap(x => (x.op === 'or' ? x.xs : [x]))) {
    if (x.op === 'const') { if (x.v) return T; continue }
    if (out.some(y => same(x, y))) continue
    if (out.some(y => (y.op === 'not' && same(y.x, x)) || (x.op === 'not' && same(x.x, y)))) return T
    out.push(x)
  }
  // Absorption: a ∨ (¬a ∧ b) is a ∨ b.
  for (let i = 0; i < out.length; i++) {
    const d = out[i]!
    if (d.op !== 'and') continue
    const parts = d.xs.filter(x => !out.some((y, j) => j !== i && x.op === 'not' && same(x.x, y)))
    if (parts.length !== d.xs.length) { out[i] = and(...parts); return or(...out) }
  }
  // A choice is one of its values: all of them together always hold.
  const iss = out.filter((x): x is Extract<B, {op: 'is'}> => x.op === 'is' && x.l.op === 'var')
  for (const a of iss) { const l = a.l as Extract<L, {op: 'var'}>; if (l.values.every(v => iss.some(b => b.value === v && same(b.l, l)))) return T }
  return out.length === 0 ? F : out.length === 1 ? out[0]! : {op: 'or', xs: out}
}
export const not = (x: B): B => (x.op === 'const' ? (x.v ? F : T) : x.op === 'not' ? x.x : {op: 'not', x})
export const bite = (c: B, a: B, b: B): B => {
  if (c.op === 'const') return c.v ? a : b
  if (same(a, b)) return a
  if (a.op === 'const' && b.op === 'const') return a.v ? c : not(c)
  // A branch that is the condition, or its negation: c ? a : ¬c is a ∨ ¬c, c ? a : c is c ∧ a, and so on.
  if (same(b, not(c))) return or(not(c), a)
  if (same(b, c)) return and(c, a)
  if (same(a, c)) return or(c, b)
  if (same(a, not(c))) return and(not(c), b)
  if (a.op === 'const') return a.v ? or(c, b) : and(not(c), b)
  if (b.op === 'const') return b.v ? or(not(c), a) : and(c, a)
  return {op: 'ite', c, a, b}
}

// --- choices and keys -----------------------------------------------------------------------------------------------
export const llit = (value: string, values: string[]): L => ({op: 'lit', value, values})
export const lite = (c: B, a: L, b: L): L => (c.op === 'const' ? (c.v ? a : b) : same(a, b) ? a : c.op === 'not' ? lite(c.x, b, a) : {op: 'ite', c, a, b})
export const is = (l: L, value: string): B => {
  if (l.op === 'lit') return l.value === value ? T : F
  if (l.op === 'ite') return bite(l.c, is(l.a, value), is(l.b, value))
  return {op: 'is', l, value}
}
export const leq = (a: L, b: L): B => (a.op === 'lit' ? is(b, a.value) : b.op === 'lit' ? is(a, b.value) : same(a, b) ? T : {op: 'leq', a, b})
export const kite = (c: B, a: K, b: K): K => (c.op === 'const' ? (c.v ? a : b) : same(a, b) ? a : {op: 'kite', c, a, b})
export const keq = (a: K, b: K): B => {
  if (same(a, b)) return T
  if (a.op === 'kite') return bite(a.c, keq(a.a, b), keq(a.b, b))
  if (b.op === 'kite') return bite(b.c, keq(a, b.a), keq(a, b.b))
  if (a.op === 'num' && b.op === 'num') return cmp('=', a.e, b.e)
  if (a.op === 'slit' && b.op === 'slit') return a.value === b.value ? T : F
  if (a.op === 'num' || b.op === 'num') return F
  return {op: 'keq', a, b}
}

// The variables a term reads, and the maps.
export function varsOf(x: N | B | L | K, out = new Set<string>(), maps = new Set<string>()): {vars: Set<string>, maps: Set<string>} {
  const go = (y: N | B | L | K): void => {
    switch (y.op) {
      case 'var': case 'svar': out.add(y.name); return
      case 'const': case 'lit': case 'slit': return
      case 'num': return go(y.e)
      case 'add': case 'sub': case 'min': case 'max': case 'mul': go(y.a); go(y.b); return
      case 'neg': case 'mulk': case 'divk': case 'modk': go(y.a); return
      case 'ite': case 'kite': go(y.c); go(y.a as N); go(y.b as N); return
      case 'cell': maps.add(y.map); go(y.key); return
      case 'cmp': case 'leq': case 'keq': go(y.a); go(y.b); return
      case 'and': case 'or': y.xs.forEach(go); return
      case 'not': go(y.x); return
      case 'is': go(y.l); return
    }
  }
  go(x)
  return {vars: out, maps}
}
