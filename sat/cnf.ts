// A tiny bit-blaster. Literals are nonzero integers (−x is not x); gates are Tseitin-encoded as they're built, so a
// circuit is its clauses. Bit-vectors are arrays of literals, least significant bit first. Variable 1 is true.
export type Lit = number
export type Vec = Lit[]

export class Circuit {
  clauses: Lit[][] = [[1]]
  vars = 1
  readonly T: Lit = 1
  readonly F: Lit = -1
  fresh(): Lit { return ++this.vars }
  input(width: number): Vec { return Array.from({length: width}, () => this.fresh()) }
  not(a: Lit): Lit { return -a }
  and(a: Lit, b: Lit): Lit {
    if (a === this.F || b === this.F || a === -b) return this.F
    if (a === this.T) return b
    if (b === this.T || a === b) return a
    const o = this.fresh()
    this.clauses.push([-o, a], [-o, b], [o, -a, -b])
    return o
  }
  or(a: Lit, b: Lit): Lit { return -this.and(-a, -b) }
  xor(a: Lit, b: Lit): Lit {
    if (a === this.F) return b
    if (b === this.F) return a
    if (a === this.T) return -b
    if (b === this.T) return -a
    if (a === b) return this.F
    if (a === -b) return this.T
    const o = this.fresh()
    this.clauses.push([-o, a, b], [-o, -a, -b], [o, -a, b], [o, a, -b])
    return o
  }
  ite(c: Lit, a: Lit, b: Lit): Lit { return this.or(this.and(c, a), this.and(-c, b)) }
  any(xs: Lit[]): Lit { return xs.reduce((acc, y) => this.or(acc, y), this.F) }
  every(xs: Lit[]): Lit { return xs.reduce((acc, y) => this.and(acc, y), this.T) }
  // Asserting a literal: a unit clause.
  assert(a: Lit) { this.clauses.push([a]) }

  // Bit-vectors.
  const(width: number, value: bigint): Vec { return Array.from({length: width}, (_, i) => ((value >> BigInt(i)) & 1n) === 1n ? this.T : this.F) }
  bnot(a: Vec): Vec { return a.map(y => -y) }
  band(a: Vec, b: Vec): Vec { return a.map((y, i) => this.and(y, b[i]!)) }
  bor(a: Vec, b: Vec): Vec { return a.map((y, i) => this.or(y, b[i]!)) }
  shr(a: Vec, k: number): Vec { return a.map((_, i) => a[i + k] ?? this.F) }
  shl(a: Vec, k: number): Vec { return a.map((_, i) => (i - k >= 0 ? a[i - k]! : this.F)) }
  eq(a: Vec, b: Vec): Lit { return this.every(a.map((y, i) => -this.xor(y, b[i]!))) }
  isZero(a: Vec): Lit { return -this.any(a) }
  bite(c: Lit, a: Vec, b: Vec): Vec { return a.map((y, i) => this.ite(c, y, b[i]!)) }
  // Ripple-carry addition, modulo 2^width.
  add(a: Vec, b: Vec): Vec {
    let carry = this.F
    return a.map((y, i) => {
      const s = this.xor(this.xor(y, b[i]!), carry)
      carry = this.or(this.and(y, b[i]!), this.and(carry, this.xor(y, b[i]!)))
      return s
    })
  }
  // Unsigned a < b: from the top bit down, the first difference has a 0 in a.
  ult(a: Vec, b: Vec): Lit {
    let lt = this.F // a < b on the bits below
    for (let i = 0; i < a.length; i++) lt = this.or(this.and(-a[i]!, b[i]!), this.and(-this.xor(a[i]!, b[i]!), lt))
    return lt
  }
  ule(a: Vec, b: Vec): Lit { return -this.ult(b, a) }
}

// A model's value of a bit-vector.
export const decode = (model: boolean[], a: Vec): bigint =>
  a.reduce((acc, y, i) => acc | ((y > 0 ? model[y]! : !model[-y]!) ? 1n << BigInt(i) : 0n), 0n)
