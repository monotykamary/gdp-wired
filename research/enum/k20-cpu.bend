import Base
# Every world of K atoms (the bits of w), counted: the reachable ones (no odd atom without the even atom below it, as
# "admin implies access"), and among them the violations of "the proposal keeps whoever the policy allows". The
# policy allows when some clause a(3i) & a(3i+1) & !a(3i+2) holds; the proposal also needs a(K-1) for clause 0.
# Leaves of 1024 worlds, forked over the high bits. Prints r * 2654435761 ^ v.

type Cnt is Data:
  C{r: U32, v: U32}

def b2u(b: Bool) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      1

def nz(+x: U32) -> U32:
  U32.xor(b2u(U32.is_zero(x)), 1)

def reach(+w: U32, +e: U32) -> U32:
  b2u(U32.is_zero(U32.and(U32.and(U32.shr(w), e), U32.not(w))))

def clauses(+w: U32, +t: U32) -> U32:
  U32.and(U32.and(U32.and(w, U32.shr(w)), U32.not(U32.shrn(w, 2n))), t)

def viol(+w: U32, +e: U32, +t: U32, +top: U32) -> U32:
  +c = clauses(w, t)
  +c2 = U32.or(U32.and(c, 4294967294), U32.and(U32.and(c, 1), nz(U32.and(w, top))))
  U32.and(U32.and(reach(w, e), nz(c)), U32.xor(nz(c2), 1))

def chunk(+j: Nat, +i: U32, +e: U32, +t: U32, +top: U32, r: U32, v: U32) -> Cnt:
  match j:
    case 0n:
      C{r, v}
    case 1n+p:
      +w = U32.add(i, U32.from_nat(p))
      chunk(p, i, e, t, top, U32.add(r, reach(w, e)), U32.add(v, viol(w, e, t, top)))

def merge(a: Cnt, b: Cnt) -> Cnt:
  match a b:
    case C{r1, v1} C{r2, v2}:
      C{U32.add(r1, r2), U32.add(v1, v2)}

def batch(+d: Nat, +i: U32, +e: U32, +t: U32, +top: U32) -> Cnt:
  match d:
    case 0n:
      chunk(1024n, i, e, t, top, 0, 0)
    case 1n+p:
      a b = batch(p, i, e, t, top) batch(p, U32.add(i, U32.shln(1024, p)), e, t, top)
      merge(a, b)

def fin(c: Cnt) -> U32:
  match c:
    case C{r, v}:
      U32.xor(U32.mul(r, 2654435761), v)

def main() -> IO(Unit):
  IO.print(U32.show(fin(batch(10n, 0, 349525, 37449, 524288))))
