// What every port of the IC3Syn suite shares (models.ts): the encoding of models.ts one level up (README.md there), plus
// the two ways a TLA+ spec's quorums are written, and the small instance each port is checked on against TLC (check.ts).
import {type Cond, type Term, all, bool, everyKey, upTo} from '../../../core/dsl.ts'
import {N, type Protocol as Base} from '../models.ts'

export {N}
export const rel = bool.from(false), relTrue = bool.from(true)
export const few = (k: number, init = 0) => upTo(k).from(init)
export const pk = (a: Term, b: Term) => a.times(N).plus(b)
export const pk3 = (a: Term, b: Term, c: Term) => a.times(N * N).plus(b.times(N)).plus(c)
export const lt = (...ts: Term[]) => ts.map(t => t.lt(N)).reduce((a, b) => a.and(b))
export const below = (n: Term, ...ts: Term[]) => ts.map(t => t.lt(n)).reduce((a, b) => a.and(b))

// A majority of the nodes 0 .. size − 1 (TLA+'s {Q \in SUBSET Node : Cardinality(Q) * 2 > Cardinality(Node)}), stated
// exactly, with no axiom: Q is within 0 .. size − 1, and the nodes outside it are fewer than half, by an injective rank
// Out[k] < c on them with 2c < size (a request carries Q and Out, and names c). For any majority Q, c = |Node \ Q| and
// a numbering of Node \ Q make it hold; where it holds, |Node \ Q| <= c < size / 2. Counting, which no EPR prover has.
export const majority = (Q: any, Out: any, c: Term, size: Term): Cond => all(
  everyKey(k => Q.at(k).atMost(1).and(Q.has(k).implies(k.lt(size)))),
  everyKey(k => k.lt(size).and(Q.has(k).not()).implies(Out.at(k).lt(c))),
  everyKey((k, j) => k.lt(size).and(j.lt(size), Q.has(k).not(), Q.has(j).not(), k.eq(j).not()).implies(Out.at(k).eq(Out.at(j)).not())),
  c.times(2).lt(size),
)
// The witness a run gives majority(): c and Out for the set Q of 0 .. size − 1.
export const majorityWitness = (q: number[], size: number) => {
  const out = new Map<number, number>(), rest = Array.from({length: size}, (_, k) => k).filter(k => !q.includes(k))
  rest.forEach((k, i) => out.set(k, i))
  return {Q: new Map(q.map(k => [k, 1] as [number, number])), Out: out, c: rest.length}
}

// The instance a port is checked on (check.ts): its params, each input's values (a carried map's as Maps), and the
// state as the TLA+ spec's variables, so that its reachable states, counted, are TLC's distinct states on the same
// constants. A state that is no state of the spec (before an `init` or a setup phase ends) projects to undefined.
export type Read = {cell: (map: string, key: number) => number, scalar: (name: string) => number}
export type Check = {
  params?: Record<string, number>,
  inputs: Record<string, (number | Map<number, number>)[]>,
  expand?: (input: Record<string, any>, r: Read) => Record<string, any>[], // a request's further values (a majority's witness)
  byState?: boolean, // expand reads the state (a witness about a state's set): computed at each state
  keep?: (r: Read) => boolean, // TLC's CONSTRAINT: a state outside it is neither counted nor explored
  uses?: string[][], // by op (its position), the inputs it reads: the others take their first value only
  project: (r: Read) => unknown,
  tlc?: {module: string, cfg: string, fix?: string[]}, // the Endive module, our cfg, a sed fix applied first
  states?: number, // TLC's distinct states, once known
}
export type Protocol = Omit<Base, 'human'> & {
  human?: Base['human'],
  ic3syn: string, file: string, // IC3Syn's name, the source file (README.md says where each is from)
  check?: Check, bad?: (r: Read) => boolean, // the instance, and the safety property broken, read there
}
export const subsets = (k: number[]): Map<number, number>[] => Array.from({length: 1 << k.length}, (_, b) => new Map(k.filter((_, j) => b >> j & 1).map(x => [x, 1] as [number, number])))
export const range = (n: number) => Array.from({length: n}, (_, i) => i)
