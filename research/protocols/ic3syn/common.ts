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

// A majority of the nodes 0 .. size − 1 (TLA+'s {Q \in SUBSET Node : Cardinality(Q) * 2 > Cardinality(Node)}), stated as
// TLA+ states it: Q is within 0 .. size − 1 (its cells 0 or 1), and its size, a count of the request (`members`: the keys
// below size where Q holds), more than half of size.
export const majority = (Q: any, members: any, size: Term): Cond => all(
  everyKey(k => Q.at(k).atMost(1).and(Q.has(k).implies(k.lt(size)))),
  size.lt(members.at(0).times(2)),
)
// The request a run gives for the set Q of 0 .. size − 1.
export const majorityWitness = (q: number[]) => ({Q: new Map(q.map(k => [k, 1] as [number, number]))})

// The instance a port is checked on (check.ts): its params, each input's values (a carried map's as Maps), and the
// state as the TLA+ spec's variables, so that its reachable states, counted, are TLC's distinct states on the same
// constants. A state that is no state of the spec (before an `init` or a setup phase ends) projects to undefined.
export type Read = {cell: (map: string, key: number) => number, scalar: (name: string) => number}
export type Check = {
  params?: Record<string, number>,
  inputs: Record<string, (number | Map<number, number>)[]>,
  expand?: (input: Record<string, any>, r?: Read) => Record<string, any>[], // a request's further values (a majority's witness)
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
