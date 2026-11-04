// Experimental, UNTRUSTED candidate selection. No equalities or verdicts escape as proofs.
import type {C, E} from '../../core/machine.ts'

export class Exhausted extends Error {}
export class Meter {
  used = 0
  constructor(readonly limit: number, readonly until = Infinity) {
    if (!Number.isSafeInteger(limit) || limit < 0) throw new Error('invalid work limit')
    if (Number.isNaN(until)) throw new Error('invalid deadline')
  }
  tick() {
    if (this.used >= this.limit || performance.now() >= this.until) throw new Exhausted('e-matching budget')
    this.used++
  }
}

// Deliberately restricted first-order fragment; unsupported terms fail closed.
function parts(e: E): [string, E[]] {
  switch (e.op) {
    case 'var': return [JSON.stringify(['var', e.name]), []]
    case 'const': return [JSON.stringify(['const', e.value]), []]
    case 'get': return [JSON.stringify(['get', e.map]), [e.key]]
    case 'mul': case 'proj': return [JSON.stringify([e.op, e.k]), [e.a]]
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup': return [e.op, [e.a, e.b]]
    case 'if': throw new Error(`unsupported e-term: ${e.op}`)
  }
}
type Node = {term: E, head: string, children: number[]}
export type Binding = Map<string, number>

export class EGraph {
  private nodes: Node[] = []
  private parent: number[] = []
  constructor(readonly meter: Meter, readonly maxNodes = 512) {
    if (!Number.isSafeInteger(maxNodes) || maxNodes < 0) throw new Error('invalid node limit')
  }
  root(i: number): number {
    this.meter.tick()
    while (this.parent[i] !== i) { this.meter.tick(); i = this.parent[i]! }
    return i
  }
  add(term: E): number {
    this.meter.tick()
    const [head, terms] = parts(term), children = terms.map(t => this.add(t))
    for (let i = 0; i < this.nodes.length; i++) {
      this.meter.tick()
      const n = this.nodes[i]!
      if (n.head === head && n.children.every((v, j) => this.root(v) === this.root(children[j]!))) return this.root(i)
    }
    if (this.nodes.length >= this.maxNodes) throw new Exhausted('e-node limit')
    const i = this.nodes.length
    this.nodes.push({term, head, children}); this.parent.push(i)
    return i
  }
  merge(a: number, b: number): boolean {
    this.meter.tick()
    a = this.root(a); b = this.root(b)
    if (a === b) return false
    this.parent[Math.max(a, b)] = Math.min(a, b)
    return true
  }
  rebuild() {
    let changed = true
    while (changed) {
      changed = false
      for (let i = 0; i < this.nodes.length; i++) for (let j = 0; j < i; j++) {
        this.meter.tick()
        const a = this.nodes[i]!, b = this.nodes[j]!
        if (a.head === b.head && a.children.every((c, k) => this.root(c) === this.root(b.children[k]!))) changed = this.merge(i, j) || changed
      }
    }
  }
  // Read all terms, but merge only positive equalities from top-level conjunctions.
  seed(cs: C[]) {
    const read = (c: C): void => {
      this.meter.tick()
      switch (c.op) {
        case '=': case '<': case '<=': this.add(c.a); this.add(c.b); return
        case 'and': case 'or': c.xs.forEach(read); return
        case 'not': read(c.x); return
        case 'flag': case 'all': throw new Error(`unsupported e-condition: ${c.op}`)
      }
    }
    const equal = (c: C): void => {
      this.meter.tick()
      if (c.op === 'and') c.xs.forEach(equal)
      else if (c.op === '=') this.merge(this.add(c.a), this.add(c.b))
    }
    cs.forEach(read); cs.forEach(equal); this.rebuild()
  }
  private *at(pattern: E, id: number, variables: Set<string>, env: Binding): Generator<Binding> {
    this.meter.tick()
    id = this.root(id)
    if (pattern.op === 'var' && variables.has(pattern.name)) {
      const old = env.get(pattern.name)
      if (old === undefined || this.root(old) === id) yield new Map([...env, [pattern.name, id]])
      return
    }
    const [head, children] = parts(pattern)
    for (let i = 0; i < this.nodes.length; i++) {
      this.meter.tick()
      const n = this.nodes[i]!
      if (this.root(i) !== id || head !== n.head) continue
      let envs = [env]
      for (let k = 0; k < children.length; k++) {
        const next: Binding[] = []
        for (const e of envs) for (const found of this.at(children[k]!, n.children[k]!, variables, e)) next.push(found)
        envs = next
      }
      yield* envs
    }
  }
  match(patterns: E[], keys: string[], maxMatches = 32): Record<string, E>[] {
    if (!Number.isSafeInteger(maxMatches) || maxMatches < 0) throw new Error('invalid match limit')
    const variables = new Set(keys), found: Record<string, E>[] = [], seen = new Set<string>()
    const join = function* (this: EGraph, k: number, env: Binding): Generator<Binding> {
      this.meter.tick()
      if (k === patterns.length) { yield env; return }
      for (let i = 0; i < this.nodes.length; i++) {
        if (this.root(i) !== i) continue
        for (const e of this.at(patterns[k]!, i, variables, env)) yield* join.call(this, k + 1, e)
      }
    }
    if (!maxMatches) return []
    for (const env of join.call(this, 0, new Map())) {
      this.meter.tick()
      if (!keys.every(k => env.has(k))) continue // never invent an unbound key
      const ids = keys.map(k => this.root(env.get(k)!)), key = JSON.stringify(ids)
      if (seen.has(key)) continue
      seen.add(key)
      found.push(Object.fromEntries(keys.map((k, i) => [k, this.nodes[ids[i]!]!.term])))
      if (found.length >= maxMatches) break
    }
    return found
  }
}
