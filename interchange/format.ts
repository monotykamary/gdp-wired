// The interchange format, version 1.0 (interchange/schema.json, docs/interchange.md): a rule, its laws and a
// certificate as JSON any language can read, write and check. Untrusted: `toInterchange` writes a certificate, and
// `fromInterchange` reads one back into the kernel's own objects, refusing whatever is outside the format. The checker
// (interchange/check.ts) reads a document with `fromInterchange`, writes it again and refuses it unless the two agree,
// so what the kernel checks is what the document says.
//
// Three choices make a document mean one thing in every language:
//   - every record whose order the kernel reads (a machine's state, its flags, a substitution) is a list of
//     [name, value] pairs in order, never a JSON object, and so is every other record, for one rule;
//   - a linear form is a list: its constant first (null when it has none), then [coefficient, atom] in the order the
//     kernel built it (a leaf's rows are found in that order, and a derivation names rows by their place);
//   - an atom is a variable's name, a map's cell {cell, key}, a monomial {mono} or a term column {col}: the i-th term of
//     the document's `columns`, a choice (∸, min, max, if) a path leaves open, named by the term itself, since the
//     kernel's own names for columns (⟦n⟧) are numbered per process.
import type {C, E, Fn, History, Law, Machine, MapUpdate, Recurrence, SomeProof, SomeWitness} from '../core/machine.ts'
import type {Fold, Goal, Helpful, Instances, KInduction, Liveness, Loop, QC, QE, QGoal, QLaw, QMachine, Rat, Recur, StepLaw, Tree} from '../kernel/kernel.ts'
import {canon, columnTerm, factorsOf, isCell, isMonomial, termColumn} from '../kernel/kernel.ts'
import type {CNode, Cyclic, Fact, Use} from '../kernel/cyclic.ts'
import type {Lin, Step} from '../core/solver.ts'

export const FORMAT = 'gdp-wired-interchange', VERSION = '1.0'

// --- the certificates, as the kernel reads them -------------------------------------------------------------------------
export type LawsProof = {instances: Record<string, Instances>, trees: Record<string, Tree>}
export type StepProof = {laws: LawsProof, instances: Instances, perStep?: Record<string, Instances>, trees: Record<string, Tree>}
export type Progress = {name: string, when: C, then: C, request: Record<string, E>}
export type Measure = {comps: {coef: number[], c: number}[]}
export type Obligation = {function: string, law: string, cyclic: Cyclic}
export type Certificate =
  | {kind: 'goals', goals: {goal: Goal, tree: Tree}[]}
  | {kind: 'laws', machine: Machine, laws: Law[], proof: LawsProof}
  | {kind: 'stepLaws', machine: Machine, laws: Law[], stepLaws: StepLaw[], proof: StepProof}
  | {kind: 'kInduction', machine: Machine, laws: Law[], kInduction: KInduction, proof: StepProof}
  | {kind: 'progress', machine: Machine, laws: Law[], progress: Progress, instances: Instances, trees: Record<string, Tree>, lawsProof?: LawsProof}
  | {kind: 'liveness', machine: Machine, laws: Law[], liveness: Liveness, proof: StepProof}
  | {kind: 'loop', loop: Loop, laws: Law[], rank: E | E[], trees: Record<string, Tree>}
  | {kind: 'recur', loop: Loop, recur: Recur}
  | {kind: 'fold', fold: Fold, laws: Law[], trees: Record<string, Tree>}
  | {kind: 'cyclic', cyclic: Cyclic}
  | {kind: 'qgoals', goals: {goal: QGoal, tree: Tree}[]}
  | {kind: 'qmachine', machine: QMachine, laws: QLaw[], trees: Record<string, {start: Tree, step: Tree}>}
  | {kind: 'termination', functions: string[], text: string, measures: Measure[], obligations: Obligation[]}
export type Kind = Certificate['kind']
export const KINDS: Kind[] = ['goals', 'laws', 'stepLaws', 'kInduction', 'progress', 'liveness', 'loop', 'recur', 'fold', 'cyclic', 'qgoals', 'qmachine', 'termination']

// A document as JSON (the parsed value). Its fields past `format`, `version`, `kind`, `meta` and `columns` are the kind's.
export type Json = null | boolean | number | string | Json[] | {[key: string]: Json | undefined}
export type Document = {format: string, version: string, kind: Kind, meta?: Json, columns?: Json[], [field: string]: Json | undefined}

// Why a value is outside the format: where, and what.
export class FormatError extends Error {}
const fail = (at: string, what: string): never => { throw new FormatError(`${at}: ${what}`) }

// --- shapes ---------------------------------------------------------------------------------------------------------------
type Obj = {[key: string]: Json | undefined}
const isObj = (x: unknown): x is Obj => typeof x === 'object' && x !== null && !Array.isArray(x)
const obj = (x: unknown, at: string, required: string[], optional: string[] = []): Obj => {
  if (!isObj(x)) fail(at, 'an object')
  const o = x as Obj
  for (const key of Object.keys(o)) if (!required.includes(key) && !optional.includes(key)) fail(at, `no field ${key}`)
  for (const key of required) if (!(key in o)) fail(at, `the field ${key}`)
  return o
}
const arr = (x: unknown, at: string): Json[] => (Array.isArray(x) ? x : fail(at, 'a list'))
const str = (x: unknown, at: string): string => (typeof x === 'string' ? x : fail(at, 'a string'))
const strs = (x: unknown, at: string): string[] => arr(x, at).map((y, i) => name(y, `${at}[${i}]`))
const bool = (x: unknown, at: string): boolean => (typeof x === 'boolean' ? x : fail(at, 'true or false'))
// Every number the format holds is a safe integer (|n| ≤ 2^53 − 1), as the kernel computes exactly only there.
const int = (x: unknown, at: string): number => (typeof x === 'number' && Number.isSafeInteger(x) ? (Object.is(x, -0) ? 0 : x) : fail(at, 'a safe integer'))
const nat = (x: unknown, at: string): number => { const n = int(x, at); return n >= 0 ? n : fail(at, 'a natural') }
// A name is a nonempty string that no JavaScript engine orders out of place: not a canonical array index (0, 7, 42),
// whose keys every engine lists first, so a record's order would not be its pairs' order.
const arrayIndex = /^(?:0|[1-9]\d*)$/
const name = (x: unknown, at: string): string => {
  const s = str(x, at)
  if (!s.length || s === '__proto__' || (arrayIndex.test(s) && Number(s) < 2 ** 32 - 1)) fail(at, `a name (nonempty, not __proto__, not a number like ${JSON.stringify(s)})`)
  return s
}
// A record as [name, value] pairs, in order; and back, each name once.
const pairs = <V>(r: Record<string, V>, f: (v: V, at: string) => Json, at: string): Json[] => Object.entries(r).map(([k, v]) => [name(k, at), f(v, `${at}.${k}`)])
const record = <V>(x: unknown, f: (v: Json, at: string) => V, at: string): Record<string, V> => {
  const out: Record<string, V> = {}
  for (const [i, p] of arr(x, at).entries()) {
    const pr = arr(p, `${at}[${i}]`)
    if (pr.length !== 2) fail(`${at}[${i}]`, 'a pair [name, value]')
    const k = name(pr[0], `${at}[${i}][0]`)
    if (Object.hasOwn(out, k)) fail(`${at}[${i}]`, `${k} twice`)
    out[k] = f(pr[1]!, `${at}.${k}`)
  }
  return out
}
const opt = <T>(o: Obj, key: string, f: (x: Json, at: string) => T, at: string): T | undefined => (key in o ? f(o[key]!, `${at}.${key}`) : undefined)
// An object with its optional fields set only where present (so a value read back equals the value written).
const clean = <T extends object>(o: T): T => Object.fromEntries(Object.entries(o).filter(([, v]) => v !== undefined)) as T

// --- terms and conditions (Lean's E and C: every constant and factor a natural) --------------------------------------------
export function encE(e: E, at = 'term'): Json {
  if (!isObj(e)) fail(at, 'a term')
  switch (e.op) {
    case 'var': return {op: e.op, name: name(e.name, `${at}.name`)}
    case 'const': return {op: e.op, value: nat(e.value, `${at}.value`)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': return {op: e.op, a: encE(e.a, `${at}.a`), b: encE(e.b, `${at}.b`)}
    case 'mul': return {op: e.op, k: nat(e.k, `${at}.k`), a: encE(e.a, `${at}.a`)}
    case 'if': return {op: e.op, c: encC(e.c, `${at}.c`), then: encE(e.then, `${at}.then`), else: encE(e.else, `${at}.else`)}
    case 'get': return {op: e.op, map: name(e.map, `${at}.map`), key: encE(e.key, `${at}.key`)}
    default: return fail(at, `no term op ${JSON.stringify((e as {op: unknown}).op)}`)
  }
}
export function decE(x: unknown, at = 'term'): E {
  if (!isObj(x)) fail(at, 'a term')
  const o = x as Obj, op = typeof o.op === 'string' ? o.op : ''
  switch (op) {
    case 'var': obj(o, at, ['op', 'name']); return {op: 'var', name: name(o.name, `${at}.name`)}
    case 'const': obj(o, at, ['op', 'value']); return {op: 'const', value: nat(o.value, `${at}.value`)}
    case 'add': case 'sub': case 'min': case 'max': case 'prod': obj(o, at, ['op', 'a', 'b']); return {op, a: decE(o.a, `${at}.a`), b: decE(o.b, `${at}.b`)}
    case 'mul': obj(o, at, ['op', 'k', 'a']); return {op: 'mul', k: nat(o.k, `${at}.k`), a: decE(o.a, `${at}.a`)}
    case 'if': obj(o, at, ['op', 'c', 'then', 'else']); return {op: 'if', c: decC(o.c, `${at}.c`), then: decE(o.then, `${at}.then`), else: decE(o.else, `${at}.else`)}
    case 'get': obj(o, at, ['op', 'map', 'key']); return {op: 'get', map: name(o.map, `${at}.map`), key: decE(o.key, `${at}.key`)}
    default: return fail(at, `no term op ${JSON.stringify(o.op ?? null)}`)
  }
}
export function encC(c: C, at = 'condition'): Json {
  if (!isObj(c)) fail(at, 'a condition')
  switch (c.op) {
    case '<': case '<=': case '=': return {op: c.op, a: encE(c.a, `${at}.a`), b: encE(c.b, `${at}.b`)}
    case 'and': case 'or': return {op: c.op, xs: arr(c.xs, `${at}.xs`).map((y, i) => encC(y as C, `${at}.xs[${i}]`))}
    case 'not': return {op: c.op, x: encC(c.x, `${at}.x`)}
    case 'flag': return {op: c.op, name: name(c.name, `${at}.name`)}
    case 'all': return clean({op: c.op, key: name(c.key, `${at}.key`), keys: c.keys === undefined ? undefined : strs(c.keys, `${at}.keys`), c: encC(c.c, `${at}.c`), witness: c.witness === undefined ? undefined : encE(c.witness, `${at}.witness`)})
    default: return fail(at, `no condition op ${JSON.stringify((c as {op: unknown}).op)}`)
  }
}
export function decC(x: unknown, at = 'condition'): C {
  if (!isObj(x)) fail(at, 'a condition')
  const o = x as Obj, op = typeof o.op === 'string' ? o.op : ''
  switch (op) {
    case '<': case '<=': case '=': obj(o, at, ['op', 'a', 'b']); return {op, a: decE(o.a, `${at}.a`), b: decE(o.b, `${at}.b`)}
    case 'and': case 'or': obj(o, at, ['op', 'xs']); return {op, xs: arr(o.xs, `${at}.xs`).map((y, i) => decC(y, `${at}.xs[${i}]`))}
    case 'not': obj(o, at, ['op', 'x']); return {op: 'not', x: decC(o.x, `${at}.x`)}
    case 'flag': obj(o, at, ['op', 'name']); return {op: 'flag', name: name(o.name, `${at}.name`)}
    case 'all': obj(o, at, ['op', 'key', 'c'], ['keys', 'witness']); return clean({op: 'all', key: name(o.key, `${at}.key`), keys: opt(o, 'keys', strs, at), c: decC(o.c, `${at}.c`), witness: opt(o, 'witness', decE, at)})
    default: return fail(at, `no condition op ${JSON.stringify(o.op ?? null)}`)
  }
}

// --- rationals (Rationals.lean's Q.E and Q.C) ----------------------------------------------------------------------------
// A rational is its numerator and denominator as decimal strings (any size; the denominator positive).
const encRat = (q: Rat, at: string): Json => (typeof q?.num === 'bigint' && typeof q.den === 'bigint' && q.den > 0n ? {num: q.num.toString(), den: q.den.toString()} : fail(at, 'a rational with a positive denominator'))
const decRat = (x: unknown, at: string): Rat => {
  const o = obj(x, at, ['num', 'den']), num = str(o.num, `${at}.num`), den = str(o.den, `${at}.den`)
  if (!/^-?(?:0|[1-9]\d*)$/.test(num) || !/^[1-9]\d*$/.test(den)) fail(at, 'a numerator (an integer) and a denominator (a positive integer) in decimal')
  return {num: BigInt(num), den: BigInt(den)}
}
export function encQE(e: QE, at = 'term'): Json {
  if (!isObj(e)) fail(at, 'a rational term')
  switch (e.op) {
    case 'var': return {op: e.op, name: name(e.name, `${at}.name`)}
    case 'const': return {op: e.op, q: encRat(e.q, `${at}.q`)}
    case 'add': case 'sub': case 'min': case 'max': return {op: e.op, a: encQE(e.a, `${at}.a`), b: encQE(e.b, `${at}.b`)}
    case 'mul': return {op: e.op, k: encRat(e.k, `${at}.k`), a: encQE(e.a, `${at}.a`)}
    case 'if': return {op: e.op, c: encQC(e.c, `${at}.c`), then: encQE(e.then, `${at}.then`), else: encQE(e.else, `${at}.else`)}
    default: return fail(at, `no rational term op ${JSON.stringify((e as {op: unknown}).op)}`)
  }
}
export function decQE(x: unknown, at = 'term'): QE {
  if (!isObj(x)) fail(at, 'a rational term')
  const o = x as Obj, op = typeof o.op === 'string' ? o.op : ''
  switch (op) {
    case 'var': obj(o, at, ['op', 'name']); return {op: 'var', name: name(o.name, `${at}.name`)}
    case 'const': obj(o, at, ['op', 'q']); return {op: 'const', q: decRat(o.q, `${at}.q`)}
    case 'add': case 'sub': case 'min': case 'max': obj(o, at, ['op', 'a', 'b']); return {op, a: decQE(o.a, `${at}.a`), b: decQE(o.b, `${at}.b`)}
    case 'mul': obj(o, at, ['op', 'k', 'a']); return {op: 'mul', k: decRat(o.k, `${at}.k`), a: decQE(o.a, `${at}.a`)}
    case 'if': obj(o, at, ['op', 'c', 'then', 'else']); return {op: 'if', c: decQC(o.c, `${at}.c`), then: decQE(o.then, `${at}.then`), else: decQE(o.else, `${at}.else`)}
    default: return fail(at, `no rational term op ${JSON.stringify(o.op ?? null)}`)
  }
}
export function encQC(c: QC, at = 'condition'): Json {
  if (!isObj(c)) fail(at, 'a rational condition')
  switch (c.op) {
    case '<': case '<=': case '=': return {op: c.op, a: encQE(c.a, `${at}.a`), b: encQE(c.b, `${at}.b`)}
    case 'and': case 'or': return {op: c.op, a: encQC(c.a, `${at}.a`), b: encQC(c.b, `${at}.b`)}
    case 'not': return {op: c.op, x: encQC(c.x, `${at}.x`)}
    default: return fail(at, `no rational condition op ${JSON.stringify((c as {op: unknown}).op)}`)
  }
}
export function decQC(x: unknown, at = 'condition'): QC {
  if (!isObj(x)) fail(at, 'a rational condition')
  const o = x as Obj, op = typeof o.op === 'string' ? o.op : ''
  switch (op) {
    case '<': case '<=': case '=': obj(o, at, ['op', 'a', 'b']); return {op, a: decQE(o.a, `${at}.a`), b: decQE(o.b, `${at}.b`)}
    case 'and': case 'or': obj(o, at, ['op', 'a', 'b']); return {op, a: decQC(o.a, `${at}.a`), b: decQC(o.b, `${at}.b`)}
    case 'not': obj(o, at, ['op', 'x']); return {op: 'not', x: decQC(o.x, `${at}.x`)}
    default: return fail(at, `no rational condition op ${JSON.stringify(o.op ?? null)}`)
  }
}

// --- linear forms, atoms and term columns -----------------------------------------------------------------------------------
// While a document is written, its columns: each term once, numbered as first met. While one is read, its table.
type Columns = {terms: Json[], index: Map<string, number>} | {read: E[]}
// A cell's key as the kernel writes it (canon: `name:coef` joined by ',', a name itself a cell or a monomial maybe).
const parseKey = (text: string): Lin => {
  const lin: Lin = {}
  let depth = 0, start = 0
  for (let i = 0; i <= text.length; i++) {
    const ch = text[i]
    if (ch === '[') depth++
    else if (ch === ']') depth--
    else if ((ch === ',' && depth === 0) || i === text.length) {
      if (i > start) { const part = text.slice(start, i), j = part.lastIndexOf(':'); lin[part.slice(0, j)] = Number(part.slice(j + 1)) }
      start = i + 1
    }
  }
  return lin
}
// A variable's name has none of the characters the kernel builds cells, monomials and columns with.
const plain = /^[^*[\],:⟦⟧]+$/
function encAtom(key: string, cols: Columns, at: string): Json {
  if (!('terms' in cols)) throw new Error('writing reads no table')
  const col = /^⟦\d+⟧$/.test(key) ? columnTerm(key) : undefined
  if (col) {
    const term = encE(col, `${at} (a column's term)`), id = JSON.stringify(term)
    let i = cols.index.get(id)
    if (i === undefined) { i = cols.terms.length; cols.index.set(id, i); cols.terms.push(term) }
    return {col: i}
  }
  if (isMonomial(key)) return {mono: factorsOf(key).map((f, i) => encAtom(f, cols, `${at}.mono[${i}]`))}
  if (isCell(key)) {
    const map = key.slice(0, key.indexOf('[')), inner = key.slice(key.indexOf('[') + 1, -1)
    // (a cell's name is the kernel's canon of its key: written back from the key read, it must be the same text)
    const lin = parseKey(inner)
    if (canon(lin) !== inner) fail(at, `a cell whose key ${inner} isn't one the kernel writes`)
    return {cell: name(map, at), key: encLin(lin, cols, `${at}.key`)}
  }
  if (key === '1' || !plain.test(key)) fail(at, `no atom ${JSON.stringify(key)}`)
  return name(key, at)
}
function decAtom(x: unknown, cols: Columns, at: string): string {
  if (!('read' in cols)) throw new Error('reading writes no table')
  if (typeof x === 'string') return x !== '1' && plain.test(x) ? name(x, at) : fail(at, `a variable's name (not 1, none of * [ ] , : ⟦ ⟧): ${JSON.stringify(x)}`)
  const o = isObj(x) ? x : fail(at, 'an atom: a name, {cell, key}, {mono} or {col}')
  if ('col' in o) {
    obj(o, at, ['col'])
    const i = nat(o.col, `${at}.col`), t = cols.read[i]
    return t ? termColumn(t) : fail(at, `column ${i} of ${cols.read.length}`)
  }
  if ('mono' in o) {
    obj(o, at, ['mono'])
    const fs = arr(o.mono, `${at}.mono`).map((f, i) => decAtom(f, cols, `${at}.mono[${i}]`))
    if (fs.length < 2 || fs.some(f => !isCell(f) && !plain.test(f))) fail(at, 'a monomial: two factors or more, each a variable or a cell')
    // (the kernel's name for a product: its factors' names sorted, joined by *)
    return [...fs].sort().join('*')
  }
  obj(o, at, ['cell', 'key'])
  return `${name(o.cell, `${at}.cell`)}[${canon(decLin(o.key, cols, `${at}.key`))}]`
}
export function encLin(lin: Lin, cols: Columns, at = 'row'): Json {
  if (!isObj(lin)) fail(at, 'a linear form')
  const out: Json[] = ['1' in lin ? int(lin['1'], `${at}[1]`) : null]
  for (const key of Object.keys(lin)) if (key !== '1') out.push([int(lin[key], `${at}[${key}]`), encAtom(key, cols, `${at}[${key}]`)])
  return out
}
export function decLin(x: unknown, cols: Columns, at = 'row'): Lin {
  const xs = arr(x, at)
  if (!xs.length) fail(at, 'a linear form: its constant (or null), then [coefficient, atom] pairs')
  const out: Lin = {}
  if (xs[0] !== null) out['1'] = int(xs[0], `${at}[0]`)
  for (const [i, t] of xs.slice(1).entries()) {
    const p = arr(t, `${at}[${i + 1}]`)
    if (p.length !== 2) fail(`${at}[${i + 1}]`, 'a pair [coefficient, atom]')
    const key = decAtom(p[1], cols, `${at}[${i + 1}][1]`)
    if (Object.hasOwn(out, key)) fail(`${at}[${i + 1}]`, `the atom ${key} twice`)
    out[key] = int(p[0], `${at}[${i + 1}][0]`)
  }
  return out
}

// --- trees: splits on atoms, a derivation at each leaf --------------------------------------------------------------------
const encStep = (s: Step, at: string): Json => {
  switch (s?.kind) {
    case 'input': return ['input', nat(s.index, `${at}.index`)]
    case 'combine': return ['combine', int(s.a, `${at}.a`), int(s.b, `${at}.b`), int(s.ma, `${at}.ma`), int(s.mb, `${at}.mb`)]
    case 'cut': return ['cut', int(s.of, `${at}.of`), int(s.g, `${at}.g`)]
    default: return fail(at, 'a step: input, combine or cut')
  }
}
const decStep = (x: unknown, at: string): Step => {
  const s = arr(x, at)
  if (s[0] === 'input' && s.length === 2) return {kind: 'input', index: nat(s[1], `${at}[1]`)}
  if (s[0] === 'combine' && s.length === 5) return {kind: 'combine', a: int(s[1], `${at}[1]`), b: int(s[2], `${at}[2]`), ma: int(s[3], `${at}[3]`), mb: int(s[4], `${at}[4]`)}
  if (s[0] === 'cut' && s.length === 3) return {kind: 'cut', of: int(s[1], `${at}[1]`), g: int(s[2], `${at}[2]`)}
  return fail(at, 'a step: ["input", i], ["combine", a, b, ma, mb] or ["cut", of, g]')
}
export function encTree(t: Tree, cols: Columns, at = 'tree'): Json {
  if (!isObj(t)) fail(at, 'a tree')
  if ('split' in t) {
    if (Object.keys(t).some(k => !['split', 'yes', 'no'].includes(k))) fail(at, `a split has split, yes and no (not ${Object.keys(t).join(', ')})`)
    return {split: encLin(t.split, cols, `${at}.split`), yes: encTree(t.yes, cols, `${at}.yes`), no: encTree(t.no, cols, `${at}.no`)}
  }
  if (Object.keys(t).some(k => !['leaf', 'products', 'squares'].includes(k))) fail(at, `a leaf has leaf, products and squares (not ${Object.keys(t).join(', ')})`)
  return clean({leaf: arr(t.leaf, `${at}.leaf`).map((s, i) => encStep(s as Step, `${at}.leaf[${i}]`)),
    products: t.products === undefined ? undefined : t.products.map((p, i) => (Array.isArray(p) && p.length === 2 ? [nat(p[0], `${at}.products[${i}]`), nat(p[1], `${at}.products[${i}]`)] : fail(`${at}.products[${i}]`, 'a pair of rows'))),
    squares: t.squares === undefined ? undefined : t.squares.map((l, i) => encLin(l, cols, `${at}.squares[${i}]`))})
}
export function decTree(x: unknown, cols: Columns, at = 'tree'): Tree {
  const o = isObj(x) ? x : fail(at, 'a tree')
  if ('split' in o) { obj(o, at, ['split', 'yes', 'no']); return {split: decLin(o.split, cols, `${at}.split`), yes: decTree(o.yes, cols, `${at}.yes`), no: decTree(o.no, cols, `${at}.no`)} }
  obj(o, at, ['leaf'], ['products', 'squares'])
  return clean({leaf: arr(o.leaf, `${at}.leaf`).map((s, i) => decStep(s, `${at}.leaf[${i}]`)),
    products: opt(o, 'products', (p, a) => arr(p, a).map((q, i): [number, number] => { const r = arr(q, `${a}[${i}]`); return r.length === 2 ? [nat(r[0], `${a}[${i}][0]`), nat(r[1], `${a}[${i}][1]`)] : fail(`${a}[${i}]`, 'a pair of rows') }), at),
    squares: opt(o, 'squares', (s, a) => arr(s, a).map((l, i) => decLin(l, cols, `${a}[${i}]`)), at)})
}
const encTrees = (ts: Record<string, Tree>, cols: Columns, at: string): Json => (isObj(ts) ? Object.entries(ts).map(([n, t]) => [str(n, at), encTree(t, cols, `${at}.${n}`)]) : fail(at, 'trees by goal'))
// (goal names are any strings: the kernel writes them, `law @start`, `node: use 2, its hypothesis 0`)
const decTrees = (x: unknown, cols: Columns, at: string): Record<string, Tree> => {
  const out: Record<string, Tree> = {}
  for (const [i, p] of arr(x, at).entries()) {
    const pr = arr(p, `${at}[${i}]`)
    if (pr.length !== 2) fail(`${at}[${i}]`, 'a pair [goal, tree]')
    const g = str(pr[0], `${at}[${i}][0]`)
    if (Object.hasOwn(out, g) || g === '__proto__') fail(`${at}[${i}]`, `the goal ${g} twice`)
    out[g] = decTree(pr[1], cols, `${at}.${g}`)
  }
  return out
}

// --- machines, laws and the rest of the subjects ----------------------------------------------------------------------------
const encMapUpdate = (w: MapUpdate, at: string): Json => ('each' in w ? {each: name(w.each, `${at}.each`), value: encE(w.value, `${at}.value`)} : {key: encE(w.key, `${at}.key`), value: encE(w.value, `${at}.value`)})
const decMapUpdate = (x: unknown, at: string): MapUpdate => {
  const o = isObj(x) ? x : fail(at, 'a write')
  if ('each' in o) { obj(o, at, ['each', 'value']); return {each: name(o.each, `${at}.each`), value: decE(o.value, `${at}.value`)} }
  obj(o, at, ['key', 'value'])
  return {key: decE(o.key, `${at}.key`), value: decE(o.value, `${at}.value`)}
}
const encHistory = (h: History, at: string): Json => clean({keep: encC(h.keep, `${at}.keep`), record: strs(h.record, `${at}.record`), sums: pairs(h.sums, encE, `${at}.sums`), queries: pairs(h.queries, encE, `${at}.queries`),
  relations: h.relations?.map((r, i) => ({when: encC(r.when, `${at}.relations[${i}].when`), holds: encC(r.holds, `${at}.relations[${i}].holds`)})),
  prune: h.prune && {order: name(h.prune.order, `${at}.prune.order`), after: encE(h.prune.after, `${at}.prune.after`)}})
const decHistory = (x: unknown, at: string): History => {
  const o = obj(x, at, ['keep', 'record', 'sums', 'queries'], ['relations', 'prune'])
  return clean({keep: decC(o.keep, `${at}.keep`), record: strs(o.record, `${at}.record`), sums: record(o.sums, decE, `${at}.sums`), queries: record(o.queries, decE, `${at}.queries`),
    relations: opt(o, 'relations', (r, a) => arr(r, a).map((y, i) => { const q = obj(y, `${a}[${i}]`, ['when', 'holds']); return {when: decC(q.when, `${a}[${i}].when`), holds: decC(q.holds, `${a}[${i}].holds`)} }), at),
    prune: opt(o, 'prune', (p, a) => { const q = obj(p, a, ['order', 'after']); return {order: name(q.order, `${a}.order`), after: decE(q.after, `${a}.after`)} }, at)})
}
const encLawLike = (l: {name: string, holds: C}, at: string): Json => ({name: str(l.name, `${at}.name`), holds: encC(l.holds, `${at}.holds`)})
const decLawLike = (x: unknown, at: string): {name: string, holds: C} => { const o = obj(x, at, ['name', 'holds']); return {name: str(o.name, `${at}.name`), holds: decC(o.holds, `${at}.holds`)} }
const encRecurrence = (r: Recurrence, at: string): Json => clean({args: strs(r.args, `${at}.args`), zero: encE(r.zero, `${at}.zero`), next: encE(r.next, `${at}.next`),
  lemmas: r.lemmas.map((l, i) => encLawLike(l, `${at}.lemmas[${i}]`)), between: r.between.map((l, i) => encLawLike(l, `${at}.between[${i}]`)),
  uses: pairs(r.uses, (u, a) => clean({arity: nat(u.arity, `${a}.arity`), lean: u.lean === undefined ? undefined : str(u.lean, `${a}.lean`)}), `${at}.uses`),
  proofs: r.proofs && clean({lemmas: r.proofs.lemmas && encML(r.proofs.lemmas, `${at}.proofs.lemmas`), between: r.proofs.between && encML(r.proofs.between, `${at}.proofs.between`)})})
const decRecurrence = (x: unknown, at: string): Recurrence => {
  const o = obj(x, at, ['args', 'zero', 'next', 'lemmas', 'between', 'uses'], ['proofs'])
  return clean({args: strs(o.args, `${at}.args`), zero: decE(o.zero, `${at}.zero`), next: decE(o.next, `${at}.next`),
    lemmas: arr(o.lemmas, `${at}.lemmas`).map((l, i) => decLawLike(l, `${at}.lemmas[${i}]`)), between: arr(o.between, `${at}.between`).map((l, i) => decLawLike(l, `${at}.between[${i}]`)),
    uses: record(o.uses, (u, a) => { const q = obj(u, a, ['arity'], ['lean']); return clean({arity: nat(q.arity, `${a}.arity`), lean: opt(q, 'lean', str, a)}) }, `${at}.uses`),
    proofs: opt(o, 'proofs', (p, a) => { const q = obj(p, a, [], ['lemmas', 'between']); return clean({lemmas: opt(q, 'lemmas', decML, a), between: opt(q, 'between', decML, a)}) }, at)})
}
const encML = (x: {machine: Machine, laws: Law[]}, at: string): Json => ({machine: encMachine(x.machine, `${at}.machine`), laws: x.laws.map((l, i) => encLaw(l, `${at}.laws[${i}]`))})
const decML = (x: unknown, at: string): {machine: Machine, laws: Law[]} => { const o = obj(x, at, ['machine', 'laws']); return {machine: decMachine(o.machine, `${at}.machine`), laws: decLaws(o.laws, `${at}.laws`)} }
const encFn = (f: Fn, at: string): Json => clean({js: str(f.js, `${at}.js`), lean: f.lean === undefined ? undefined : str(f.lean, `${at}.lean`), recur: f.recur && encRecurrence(f.recur, `${at}.recur`),
  arity: f.arity === undefined ? undefined : nat(f.arity, `${at}.arity`), call: f.call === undefined ? undefined : str(f.call, `${at}.call`)})
const decFn = (x: unknown, at: string): Fn => {
  const o = obj(x, at, ['js'], ['lean', 'recur', 'arity', 'call'])
  return clean({js: str(o.js, `${at}.js`), lean: opt(o, 'lean', str, at), recur: opt(o, 'recur', decRecurrence, at), arity: opt(o, 'arity', nat, at), call: opt(o, 'call', str, at)})
}
export function encMachine(m: Machine, at = 'machine'): Json {
  if (!isObj(m)) fail(at, 'a machine')
  for (const key of Object.keys(m)) if (!['name', 'params', 'inputs', 'state', 'maps', 'inputMaps', 'step', 'pre', 'assume', 'history', 'fns', 'facts'].includes(key) && (m as Record<string, unknown>)[key] !== undefined) fail(at, `no field ${key}`)
  const s = m.step
  if (!isObj(s) || Object.keys(s).some(k => !['flags', 'state', 'maps'].includes(k) && (s as Record<string, unknown>)[k] !== undefined)) fail(`${at}.step`, 'a step: flags, state and maps')
  return clean({name: str(m.name, `${at}.name`), params: strs(m.params, `${at}.params`), inputs: strs(m.inputs, `${at}.inputs`), state: pairs(m.state, encE, `${at}.state`),
    maps: m.maps && pairs(m.maps, nat, `${at}.maps`), inputMaps: m.inputMaps && strs(m.inputMaps, `${at}.inputMaps`),
    step: clean({flags: s.flags && pairs(s.flags, encC, `${at}.step.flags`), state: s.state && pairs(s.state, encE, `${at}.step.state`), maps: s.maps && pairs(s.maps, encMapUpdate, `${at}.step.maps`)}),
    pre: m.pre && encC(m.pre, `${at}.pre`), assume: m.assume && encC(m.assume, `${at}.assume`), history: m.history && encHistory(m.history, `${at}.history`),
    fns: m.fns && pairs(m.fns, encFn, `${at}.fns`), facts: m.facts && m.facts.map((l, i) => encLaw(l, `${at}.facts[${i}]`))})
}
export function decMachine(x: unknown, at = 'machine'): Machine {
  const o = obj(x, at, ['name', 'params', 'inputs', 'state', 'step'], ['maps', 'inputMaps', 'pre', 'assume', 'history', 'fns', 'facts'])
  const s = obj(o.step, `${at}.step`, [], ['flags', 'state', 'maps'])
  return clean({name: str(o.name, `${at}.name`), params: strs(o.params, `${at}.params`), inputs: strs(o.inputs, `${at}.inputs`), state: record(o.state, decE, `${at}.state`),
    maps: opt(o, 'maps', (y, a) => record(y, nat, a), at), inputMaps: opt(o, 'inputMaps', strs, at),
    step: clean({flags: opt(s, 'flags', (y, a) => record(y, decC, a), `${at}.step`), state: opt(s, 'state', (y, a) => record(y, decE, a), `${at}.step`), maps: opt(s, 'maps', (y, a) => record(y, decMapUpdate, a), `${at}.step`)}),
    pre: opt(o, 'pre', decC, at), assume: opt(o, 'assume', decC, at), history: opt(o, 'history', decHistory, at), fns: opt(o, 'fns', (y, a) => record(y, decFn, a), at), facts: opt(o, 'facts', decLaws, at)})
}
const encWitness = (w: SomeWitness, at: string): Json => clean({terms: w.terms && pairs(w.terms, encE, `${at}.terms`), ghost: w.ghost && pairs(w.ghost, (g, a) => ({start: encE(g.start, `${a}.start`), step: encE(g.step, `${a}.step`)}), `${at}.ghost`)})
const decWitness = (x: unknown, at: string): SomeWitness => {
  const o = obj(x, at, [], ['terms', 'ghost'])
  return clean({terms: opt(o, 'terms', (y, a) => record(y, decE, a), at), ghost: opt(o, 'ghost', (y, a) => record(y, (g, b) => { const q = obj(g, b, ['start', 'step']); return {start: decE(q.start, `${b}.start`), step: decE(q.step, `${b}.step`)} }, a), at)})
}
const encEx = (e: SomeProof, at: string): Json => clean({vars: strs(e.vars, `${at}.vars`), body: encC(e.body, `${at}.body`), sub: e.sub && pairs(e.sub, encE, `${at}.sub`), ghost: e.ghost === undefined ? undefined : e.ghost === true ? true : fail(`${at}.ghost`, 'true')})
const decEx = (x: unknown, at: string): SomeProof => {
  const o = obj(x, at, ['vars', 'body'], ['sub', 'ghost'])
  return clean({vars: strs(o.vars, `${at}.vars`), body: decC(o.body, `${at}.body`), sub: opt(o, 'sub', (y, a) => record(y, decE, a), at), ghost: opt(o, 'ghost', (y, a) => (bool(y, a) ? true as const : fail(a, 'true')), at)})
}
export function encLaw(l: Law, at = 'law'): Json {
  if (!isObj(l)) fail(at, 'a law')
  for (const key of Object.keys(l)) if (!['name', 'holds', 'forall', 'keys', 'stated', 'some', 'witness', 'ex'].includes(key) && (l as Record<string, unknown>)[key] !== undefined) fail(at, `no field ${key}`)
  return clean({name: str(l.name, `${at}.name`), holds: encC(l.holds, `${at}.holds`), forall: l.forall === undefined ? undefined : name(l.forall, `${at}.forall`), keys: l.keys && strs(l.keys, `${at}.keys`),
    stated: l.stated && encC(l.stated, `${at}.stated`), some: l.some && strs(l.some, `${at}.some`), witness: l.witness && encWitness(l.witness, `${at}.witness`), ex: l.ex && encEx(l.ex, `${at}.ex`)})
}
export function decLaw(x: unknown, at = 'law'): Law {
  const o = obj(x, at, ['name', 'holds'], ['forall', 'keys', 'stated', 'some', 'witness', 'ex'])
  return clean({name: str(o.name, `${at}.name`), holds: decC(o.holds, `${at}.holds`), forall: opt(o, 'forall', name, at), keys: opt(o, 'keys', strs, at), stated: opt(o, 'stated', decC, at),
    some: opt(o, 'some', strs, at), witness: opt(o, 'witness', decWitness, at), ex: opt(o, 'ex', decEx, at)})
}
const encLaws = (ls: Law[], at: string): Json => arr(ls, at).map((l, i) => encLaw(l as Law, `${at}[${i}]`))
const decLaws = (x: unknown, at: string): Law[] => arr(x, at).map((l, i) => decLaw(l, `${at}[${i}]`))
const encWhen = (w: C | C[], at: string): Json => (Array.isArray(w) ? w.map((c, i) => encC(c, `${at}[${i}]`)) : encC(w, at))
const decWhen = (x: unknown, at: string): C | C[] => (Array.isArray(x) ? x.map((c, i) => decC(c, `${at}[${i}]`)) : decC(x, at))
const encStepLaw = (s: StepLaw, at: string): Json => clean({name: str(s.name, `${at}.name`), when: s.when === undefined ? undefined : encWhen(s.when, `${at}.when`), then: encC(s.then, `${at}.then`),
  forall: s.forall === undefined ? undefined : name(s.forall, `${at}.forall`), keys: s.keys && strs(s.keys, `${at}.keys`), steps: s.steps === undefined ? undefined : nat(s.steps, `${at}.steps`)})
const decStepLaw = (x: unknown, at: string): StepLaw => {
  const o = obj(x, at, ['name', 'then'], ['when', 'forall', 'keys', 'steps'])
  return clean({name: str(o.name, `${at}.name`), when: opt(o, 'when', decWhen, at), then: decC(o.then, `${at}.then`), forall: opt(o, 'forall', name, at), keys: opt(o, 'keys', strs, at), steps: opt(o, 'steps', nat, at)})
}
const encRank = (r: E | E[], at: string): Json => (Array.isArray(r) ? r.map((e, i) => encE(e, `${at}[${i}]`)) : encE(r, at))
const decRank = (x: unknown, at: string): E | E[] => (Array.isArray(x) ? x.map((e, i) => decE(e, `${at}[${i}]`)) : decE(x, at))
const encHelpful = (h: Helpful, at: string): Json => clean({when: h.when && encC(h.when, `${at}.when`), request: pairs(h.request, encE, `${at}.request`)})
const decHelpful = (x: unknown, at: string): Helpful => { const o = obj(x, at, ['request'], ['when']); return clean({when: opt(o, 'when', decC, at), request: record(o.request, decE, `${at}.request`)}) }
const encLiveness = (l: Liveness, at: string): Json => clean({name: str(l.name, `${at}.name`), from: encC(l.from, `${at}.from`), to: encC(l.to, `${at}.to`), rank: encRank(l.rank, `${at}.rank`),
  request: l.request && pairs(l.request, encE, `${at}.request`), helpful: l.helpful && l.helpful.map((h, i) => encHelpful(h, `${at}.helpful[${i}]`))})
const decLiveness = (x: unknown, at: string): Liveness => {
  const o = obj(x, at, ['name', 'from', 'to', 'rank'], ['request', 'helpful'])
  return clean({name: str(o.name, `${at}.name`), from: decC(o.from, `${at}.from`), to: decC(o.to, `${at}.to`), rank: decRank(o.rank, `${at}.rank`),
    request: opt(o, 'request', (y, a) => record(y, decE, a), at), helpful: opt(o, 'helpful', (y, a) => arr(y, a).map((h, i) => decHelpful(h, `${a}[${i}]`)), at)})
}
const encLoop = (l: Loop, at: string): Json => clean({name: str(l.name, `${at}.name`), params: strs(l.params, `${at}.params`), inputs: strs(l.inputs, `${at}.inputs`), state: pairs(l.state, encE, `${at}.state`),
  while: encC(l.while, `${at}.while`), body: pairs(l.body, encE, `${at}.body`), pre: l.pre && encC(l.pre, `${at}.pre`), assume: l.assume && encC(l.assume, `${at}.assume`)})
const decLoop = (x: unknown, at: string): Loop => {
  const o = obj(x, at, ['name', 'params', 'inputs', 'state', 'while', 'body'], ['pre', 'assume'])
  return clean({name: str(o.name, `${at}.name`), params: strs(o.params, `${at}.params`), inputs: strs(o.inputs, `${at}.inputs`), state: record(o.state, decE, `${at}.state`),
    while: decC(o.while, `${at}.while`), body: record(o.body, decE, `${at}.body`), pre: opt(o, 'pre', decC, at), assume: opt(o, 'assume', decC, at)})
}
const encFold = (f: Fold, at: string): Json => clean({name: str(f.name, `${at}.name`), params: strs(f.params, `${at}.params`), inputs: strs(f.inputs, `${at}.inputs`), leaf: pairs(f.leaf, encE, `${at}.leaf`),
  node: pairs(f.node, encE, `${at}.node`), pre: f.pre && encC(f.pre, `${at}.pre`), assume: f.assume && encC(f.assume, `${at}.assume`)})
const decFold = (x: unknown, at: string): Fold => {
  const o = obj(x, at, ['name', 'params', 'inputs', 'leaf', 'node'], ['pre', 'assume'])
  return clean({name: str(o.name, `${at}.name`), params: strs(o.params, `${at}.params`), inputs: strs(o.inputs, `${at}.inputs`), leaf: record(o.leaf, decE, `${at}.leaf`),
    node: record(o.node, decE, `${at}.node`), pre: opt(o, 'pre', decC, at), assume: opt(o, 'assume', decC, at)})
}
const encQMachine = (m: QMachine, at: string): Json => clean({name: str(m.name, `${at}.name`), params: strs(m.params, `${at}.params`), inputs: strs(m.inputs, `${at}.inputs`), state: pairs(m.state, encQE, `${at}.state`),
  step: pairs(m.step, encQE, `${at}.step`), pre: m.pre && encQC(m.pre, `${at}.pre`), assume: m.assume && encQC(m.assume, `${at}.assume`)})
const decQMachine = (x: unknown, at: string): QMachine => {
  const o = obj(x, at, ['name', 'params', 'inputs', 'state', 'step'], ['pre', 'assume'])
  return clean({name: str(o.name, `${at}.name`), params: strs(o.params, `${at}.params`), inputs: strs(o.inputs, `${at}.inputs`), state: record(o.state, decQE, `${at}.state`),
    step: record(o.step, decQE, `${at}.step`), pre: opt(o, 'pre', decQC, at), assume: opt(o, 'assume', decQC, at)})
}

// --- proofs ---------------------------------------------------------------------------------------------------------------
const encInst = (i: Instances, at: string): Json => pairs(i, (es, a) => arr(es, a).map((e, j) => encE(e as E, `${a}[${j}]`)), at)
const decInst = (x: unknown, at: string): Instances => record(x, (es, a) => arr(es, a).map((e, j) => decE(e, `${a}[${j}]`)), at)
const encLawsProof = (p: LawsProof, cols: Columns, at: string): Json => ({instances: pairs(p.instances, encInst, `${at}.instances`), trees: encTrees(p.trees, cols, `${at}.trees`)})
const decLawsProof = (x: unknown, cols: Columns, at: string): LawsProof => { const o = obj(x, at, ['instances', 'trees']); return {instances: record(o.instances, decInst, `${at}.instances`), trees: decTrees(o.trees, cols, `${at}.trees`)} }
const encStepProof = (p: StepProof, cols: Columns, at: string): Json => clean({laws: encLawsProof(p.laws, cols, `${at}.laws`), instances: encInst(p.instances, `${at}.instances`),
  perStep: p.perStep && pairs(p.perStep, encInst, `${at}.perStep`), trees: encTrees(p.trees, cols, `${at}.trees`)})
const decStepProof = (x: unknown, cols: Columns, at: string): StepProof => {
  const o = obj(x, at, ['laws', 'instances', 'trees'], ['perStep'])
  return clean({laws: decLawsProof(o.laws, cols, `${at}.laws`), instances: decInst(o.instances, `${at}.instances`), perStep: opt(o, 'perStep', (y, a) => record(y, decInst, a), at), trees: decTrees(o.trees, cols, `${at}.trees`)})
}
const encCyclic = (p: Cyclic, cols: Columns, at: string): Json => ({
  facts: p.facts.map((f: Fact, i) => ({name: str(f.name, `${at}.facts[${i}].name`), keys: strs(f.keys, `${at}.facts[${i}].keys`), holds: encC(f.holds, `${at}.facts[${i}].holds`)})),
  nodes: p.nodes.map((n: CNode, i) => {
    const a = `${at}.nodes[${i}]`
    return {name: str(n.name, `${a}.name`), hyps: n.hyps.map((h, j) => encC(h, `${a}.hyps[${j}]`)), concl: encC(n.concl, `${a}.concl`), rank: n.rank.map((e, j) => encE(e, `${a}.rank[${j}]`)),
      insts: n.insts.map((t, j) => ({fact: nat(t.fact, `${a}.insts[${j}].fact`), at: t.at.map((e, l) => encE(e, `${a}.insts[${j}].at[${l}]`))})),
      uses: n.uses.map((u: Use, j) => ({node: nat(u.node, `${a}.uses[${j}].node`), subst: pairs(u.subst, encE, `${a}.uses[${j}].subst`), guard: encC(u.guard, `${a}.uses[${j}].guard`),
        premises: u.premises.map((t, l) => encTree(t, cols, `${a}.uses[${j}].premises[${l}]`)), descent: encTree(u.descent, cols, `${a}.uses[${j}].descent`)})),
      main: encTree(n.main, cols, `${a}.main`)}
  }),
})
const decCyclic = (x: unknown, cols: Columns, at: string): Cyclic => {
  const o = obj(x, at, ['facts', 'nodes'])
  return {
    facts: arr(o.facts, `${at}.facts`).map((f, i) => { const a = `${at}.facts[${i}]`, q = obj(f, a, ['name', 'keys', 'holds']); return {name: str(q.name, `${a}.name`), keys: strs(q.keys, `${a}.keys`), holds: decC(q.holds, `${a}.holds`)} }),
    nodes: arr(o.nodes, `${at}.nodes`).map((n, i) => {
      const a = `${at}.nodes[${i}]`, q = obj(n, a, ['name', 'hyps', 'concl', 'rank', 'insts', 'uses', 'main'])
      return {name: str(q.name, `${a}.name`), hyps: arr(q.hyps, `${a}.hyps`).map((h, j) => decC(h, `${a}.hyps[${j}]`)), concl: decC(q.concl, `${a}.concl`), rank: arr(q.rank, `${a}.rank`).map((e, j) => decE(e, `${a}.rank[${j}]`)),
        insts: arr(q.insts, `${a}.insts`).map((t, j) => { const b = `${a}.insts[${j}]`, r = obj(t, b, ['fact', 'at']); return {fact: nat(r.fact, `${b}.fact`), at: arr(r.at, `${b}.at`).map((e, l) => decE(e, `${b}.at[${l}]`))} }),
        uses: arr(q.uses, `${a}.uses`).map((u, j) => {
          const b = `${a}.uses[${j}]`, r = obj(u, b, ['node', 'subst', 'guard', 'premises', 'descent'])
          return {node: nat(r.node, `${b}.node`), subst: record(r.subst, decE, `${b}.subst`), guard: decC(r.guard, `${b}.guard`), premises: arr(r.premises, `${b}.premises`).map((t, l) => decTree(t, cols, `${b}.premises[${l}]`)), descent: decTree(r.descent, cols, `${b}.descent`)}
        }),
        main: decTree(q.main, cols, `${a}.main`)}
    }),
  }
}
const encRecur = (r: Recur, cols: Columns, at: string): Json => ({start: pairs(r.start, nat, `${at}.start`), stem: r.stem.map((t, i) => pairs(t, nat, `${at}.stem[${i}]`)), set: encC(r.set, `${at}.set`),
  wit: pairs(r.wit, encE, `${at}.wit`), tree: encTree(r.tree, cols, `${at}.tree`)})
const decRecur = (x: unknown, cols: Columns, at: string): Recur => {
  const o = obj(x, at, ['start', 'stem', 'set', 'wit', 'tree'])
  return {start: record(o.start, nat, `${at}.start`), stem: arr(o.stem, `${at}.stem`).map((t, i) => record(t, nat, `${at}.stem[${i}]`)), set: decC(o.set, `${at}.set`), wit: record(o.wit, decE, `${at}.wit`), tree: decTree(o.tree, cols, `${at}.tree`)}
}
const encMeasure = (m: Measure, at: string): Json => ({comps: arr(m.comps, `${at}.comps`).map((c, i) => { const q = c as Measure['comps'][number]; return {coef: arr(q.coef, `${at}.comps[${i}].coef`).map((k, j) => int(k, `${at}.comps[${i}].coef[${j}]`)), c: int(q.c, `${at}.comps[${i}].c`)} })})
const decMeasure = (x: unknown, at: string): Measure => {
  const o = obj(x, at, ['comps'])
  return {comps: arr(o.comps, `${at}.comps`).map((c, i) => { const q = obj(c, `${at}.comps[${i}]`, ['coef', 'c']); return {coef: arr(q.coef, `${at}.comps[${i}].coef`).map((k, j) => int(k, `${at}.comps[${i}].coef[${j}]`)), c: int(q.c, `${at}.comps[${i}].c`)} })}
}

// --- documents ---------------------------------------------------------------------------------------------------------------
// The fields each kind has, in the order a document is written.
const FIELDS: Record<Kind, {required: string[], optional?: string[]}> = {
  goals: {required: ['goals']}, laws: {required: ['machine', 'laws', 'proof']}, stepLaws: {required: ['machine', 'laws', 'stepLaws', 'proof']},
  kInduction: {required: ['machine', 'laws', 'kInduction', 'proof']}, progress: {required: ['machine', 'laws', 'progress', 'instances', 'trees'], optional: ['lawsProof']},
  liveness: {required: ['machine', 'laws', 'liveness', 'proof']}, loop: {required: ['loop', 'laws', 'rank', 'trees']}, recur: {required: ['loop', 'recur']},
  fold: {required: ['fold', 'laws', 'trees']}, cyclic: {required: ['cyclic']}, qgoals: {required: ['goals']}, qmachine: {required: ['machine', 'laws', 'trees']},
  termination: {required: ['functions', 'text', 'measures', 'obligations']},
}

// The certificate as a document. `meta` is anything the producer wants kept beside it (the checker reads none of it).
export function toInterchange(c: Certificate, meta?: Json): Document {
  const cols: Columns = {terms: [], index: new Map()}
  const body = ((): Record<string, Json | undefined> => {
    switch (c.kind) {
      case 'goals': return {goals: c.goals.map((g, i) => ({name: str(g.goal.name, `goals[${i}].name`), hyps: g.goal.hyps.map((h, j) => encC(h, `goals[${i}].hyps[${j}]`)), tree: encTree(g.tree, cols, `goals[${i}].tree`)}))}
      case 'laws': return {machine: encMachine(c.machine), laws: encLaws(c.laws, 'laws'), proof: encLawsProof(c.proof, cols, 'proof')}
      case 'stepLaws': return {machine: encMachine(c.machine), laws: encLaws(c.laws, 'laws'), stepLaws: c.stepLaws.map((s, i) => encStepLaw(s, `stepLaws[${i}]`)), proof: encStepProof(c.proof, cols, 'proof')}
      case 'kInduction': return {machine: encMachine(c.machine), laws: encLaws(c.laws, 'laws'), kInduction: {law: encLaw(c.kInduction.law, 'kInduction.law'), k: nat(c.kInduction.k, 'kInduction.k')}, proof: encStepProof(c.proof, cols, 'proof')}
      case 'progress': return {machine: encMachine(c.machine), laws: encLaws(c.laws, 'laws'),
        progress: {name: str(c.progress.name, 'progress.name'), when: encC(c.progress.when, 'progress.when'), then: encC(c.progress.then, 'progress.then'), request: pairs(c.progress.request, encE, 'progress.request')},
        instances: encInst(c.instances, 'instances'), trees: encTrees(c.trees, cols, 'trees'), lawsProof: c.lawsProof && encLawsProof(c.lawsProof, cols, 'lawsProof')}
      case 'liveness': return {machine: encMachine(c.machine), laws: encLaws(c.laws, 'laws'), liveness: encLiveness(c.liveness, 'liveness'), proof: encStepProof(c.proof, cols, 'proof')}
      case 'loop': return {loop: encLoop(c.loop, 'loop'), laws: encLaws(c.laws, 'laws'), rank: encRank(c.rank, 'rank'), trees: encTrees(c.trees, cols, 'trees')}
      case 'recur': return {loop: encLoop(c.loop, 'loop'), recur: encRecur(c.recur, cols, 'recur')}
      case 'fold': return {fold: encFold(c.fold, 'fold'), laws: encLaws(c.laws, 'laws'), trees: encTrees(c.trees, cols, 'trees')}
      case 'cyclic': return {cyclic: encCyclic(c.cyclic, cols, 'cyclic')}
      case 'qgoals': return {goals: c.goals.map((g, i) => ({name: str(g.goal.name, `goals[${i}].name`), hyps: g.goal.hyps.map((h, j) => encQC(h, `goals[${i}].hyps[${j}]`)), tree: encTree(g.tree, cols, `goals[${i}].tree`)}))}
      case 'qmachine': return {machine: encQMachine(c.machine, 'machine'), laws: c.laws.map((l, i) => ({name: str(l.name, `laws[${i}].name`), holds: encQC(l.holds, `laws[${i}].holds`)})),
        trees: Object.entries(c.trees).map(([n, t]) => [str(n, 'trees'), {start: encTree(t.start, cols, `trees.${n}.start`), step: encTree(t.step, cols, `trees.${n}.step`)}])}
      case 'termination': return {functions: strs(c.functions, 'functions'), text: str(c.text, 'text'), measures: c.measures.map((m, i) => encMeasure(m, `measures[${i}]`)),
        obligations: c.obligations.map((o, i) => ({function: name(o.function, `obligations[${i}].function`), law: str(o.law, `obligations[${i}].law`), cyclic: encCyclic(o.cyclic, cols, `obligations[${i}].cyclic`)}))}
      default: return fail('kind', `no kind ${JSON.stringify((c as {kind: unknown}).kind)}`)
    }
  })()
  return clean({format: FORMAT, version: VERSION, kind: c.kind, meta, columns: 'terms' in cols && cols.terms.length ? cols.terms : undefined, ...body}) as Document
}

// A document read back into the kernel's objects, or a FormatError saying where it leaves the format.
export function fromInterchange(doc: unknown): Certificate {
  const head = isObj(doc) ? doc : fail('document', 'an object')
  if (head.format !== FORMAT) fail('format', `${JSON.stringify(FORMAT)}`)
  if (head.version !== VERSION) fail('version', `${VERSION} (this reader's; a 1.0 reader reads 1.0 alone)`)
  const kind = head.kind as Kind
  if (!KINDS.includes(kind)) fail('kind', `one of ${KINDS.join(', ')}`)
  const o = obj(head, 'document', ['format', 'version', 'kind', ...FIELDS[kind].required], ['meta', 'columns', ...(FIELDS[kind].optional ?? [])])
  const cols: Columns = {read: opt(o, 'columns', (x, a) => arr(x, a).map((t, i) => decE(t, `${a}[${i}]`)), 'document') ?? []}
  switch (kind) {
    case 'goals': return {kind, goals: arr(o.goals, 'goals').map((g, i) => { const q = obj(g, `goals[${i}]`, ['name', 'hyps', 'tree']); return {goal: {name: str(q.name, `goals[${i}].name`), hyps: arr(q.hyps, `goals[${i}].hyps`).map((h, j) => decC(h, `goals[${i}].hyps[${j}]`))}, tree: decTree(q.tree, cols, `goals[${i}].tree`)} })}
    case 'laws': return {kind, machine: decMachine(o.machine), laws: decLaws(o.laws, 'laws'), proof: decLawsProof(o.proof, cols, 'proof')}
    case 'stepLaws': return {kind, machine: decMachine(o.machine), laws: decLaws(o.laws, 'laws'), stepLaws: arr(o.stepLaws, 'stepLaws').map((s, i) => decStepLaw(s, `stepLaws[${i}]`)), proof: decStepProof(o.proof, cols, 'proof')}
    case 'kInduction': { const q = obj(o.kInduction, 'kInduction', ['law', 'k']); return {kind, machine: decMachine(o.machine), laws: decLaws(o.laws, 'laws'), kInduction: {law: decLaw(q.law, 'kInduction.law'), k: nat(q.k, 'kInduction.k')}, proof: decStepProof(o.proof, cols, 'proof')} }
    case 'progress': {
      const q = obj(o.progress, 'progress', ['name', 'when', 'then', 'request'])
      return clean({kind, machine: decMachine(o.machine), laws: decLaws(o.laws, 'laws'), progress: {name: str(q.name, 'progress.name'), when: decC(q.when, 'progress.when'), then: decC(q.then, 'progress.then'), request: record(q.request, decE, 'progress.request')},
        instances: decInst(o.instances, 'instances'), trees: decTrees(o.trees, cols, 'trees'), lawsProof: opt(o, 'lawsProof', (x, a) => decLawsProof(x, cols, a), 'document')})
    }
    case 'liveness': return {kind, machine: decMachine(o.machine), laws: decLaws(o.laws, 'laws'), liveness: decLiveness(o.liveness, 'liveness'), proof: decStepProof(o.proof, cols, 'proof')}
    case 'loop': return {kind, loop: decLoop(o.loop, 'loop'), laws: decLaws(o.laws, 'laws'), rank: decRank(o.rank, 'rank'), trees: decTrees(o.trees, cols, 'trees')}
    case 'recur': return {kind, loop: decLoop(o.loop, 'loop'), recur: decRecur(o.recur, cols, 'recur')}
    case 'fold': return {kind, fold: decFold(o.fold, 'fold'), laws: decLaws(o.laws, 'laws'), trees: decTrees(o.trees, cols, 'trees')}
    case 'cyclic': return {kind, cyclic: decCyclic(o.cyclic, cols, 'cyclic')}
    case 'qgoals': return {kind, goals: arr(o.goals, 'goals').map((g, i) => { const q = obj(g, `goals[${i}]`, ['name', 'hyps', 'tree']); return {goal: {name: str(q.name, `goals[${i}].name`), hyps: arr(q.hyps, `goals[${i}].hyps`).map((h, j) => decQC(h, `goals[${i}].hyps[${j}]`))}, tree: decTree(q.tree, cols, `goals[${i}].tree`)} })}
    case 'qmachine': {
      const trees: Record<string, {start: Tree, step: Tree}> = {}
      for (const [i, p] of arr(o.trees, 'trees').entries()) {
        const pr = arr(p, `trees[${i}]`)
        if (pr.length !== 2) fail(`trees[${i}]`, 'a pair [law, {start, step}]')
        const n = str(pr[0], `trees[${i}][0]`), q = obj(pr[1], `trees.${n}`, ['start', 'step'])
        if (Object.hasOwn(trees, n) || n === '__proto__') fail(`trees[${i}]`, `the law ${n} twice`)
        trees[n] = {start: decTree(q.start, cols, `trees.${n}.start`), step: decTree(q.step, cols, `trees.${n}.step`)}
      }
      return {kind, machine: decQMachine(o.machine, 'machine'), laws: arr(o.laws, 'laws').map((l, i) => { const q = obj(l, `laws[${i}]`, ['name', 'holds']); return {name: str(q.name, `laws[${i}].name`), holds: decQC(q.holds, `laws[${i}].holds`)} }), trees}
    }
    case 'termination': return {kind, functions: strs(o.functions, 'functions'), text: str(o.text, 'text'), measures: arr(o.measures, 'measures').map((m, i) => decMeasure(m, `measures[${i}]`)),
      obligations: arr(o.obligations, 'obligations').map((x, i) => { const q = obj(x, `obligations[${i}]`, ['function', 'law', 'cyclic']); return {function: name(q.function, `obligations[${i}].function`), law: str(q.law, `obligations[${i}].law`), cyclic: decCyclic(q.cyclic, cols, `obligations[${i}].cyclic`)} })}
  }
}

// The document with each column reference replaced by its term: two documents mean the same certificate exactly when
// these agree (field order inside an object aside), whatever order their columns are numbered in.
export function resolved(doc: Document): Json {
  const cols = (doc.columns ?? []) as Json[]
  const walk = (x: Json | undefined): Json => {
    if (x === undefined) return null
    if (Array.isArray(x)) return x.map(walk)
    if (!isObj(x)) return x
    if (Object.keys(x).length === 1 && 'col' in x && typeof x.col === 'number') return {col: cols[x.col] ?? null}
    return Object.fromEntries(Object.entries(x).map(([k, v]) => [k, walk(v)]))
  }
  const {columns: _, ...rest} = doc
  void _
  return walk(rest as Json)
}
// Structural equality of JSON values, object fields in any order.
export function sameJson(a: Json | undefined, b: Json | undefined): boolean {
  if (Array.isArray(a)) return Array.isArray(b) && a.length === b.length && a.every((x, i) => sameJson(x, b[i]))
  if (isObj(a)) {
    if (!isObj(b)) return false
    const ka = Object.keys(a).filter(k => a[k] !== undefined), kb = Object.keys(b).filter(k => b[k] !== undefined)
    return ka.length === kb.length && ka.every(k => Object.hasOwn(b, k) && sameJson(a[k], b[k]))
  }
  return a === b
}
