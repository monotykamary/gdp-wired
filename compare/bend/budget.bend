# Rule 1, the budget, in Bend 2: s from 0; a request of cost c adds min(c, m)
# while s < b. Law: s <= b + m after any list of requests, proven by hand:
# induction on the list, with the step's comparison carried as evidence
# (Cmp2), since a Bend proof cannot case on a computed Bool.
import Base

# --- evidence
# a <= b as a type: Unit when it holds, Empty when it doesn't
def LE(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n y:
      Unit
    case 1n+x 0n:
      Empty
    case 1n+x 1n+y:
      LE(x, y)

# a comparison with its evidence: x <= y, or y < x
type Cmp2<-x: Nat, -y: Nat> is Data:
  IsLe{e: LE(x, y)}
  IsGt{e: LE(1n+y, x)}

def dec.up(-a: Nat, -b: Nat, w: Cmp2<a, b>) -> Cmp2<1n+a, 1n+b>:
  match w:
    case IsLe{e}:
      IsLe{e}
    case IsGt{e}:
      IsGt{e}

def dec(x: Nat, y: Nat) -> Cmp2<x, y>:
  match x y:
    case 0n y:
      IsLe{Unit{}}
    case 1n+a 0n:
      IsGt{Unit{}}
    case 1n+a 1n+b:
      dec.up(a, b, dec(a, b))

# --- rule
def step.go(s: Nat, -b: Nat, c: Nat, m: Nat, w: Cmp2<b, s>) -> Nat:
  match w:
    case IsLe{e}:
      s
    case IsGt{e}:
      Nat.add(s, Nat.min(c, m))

def step(+s: Nat, +b: Nat, c: Nat, m: Nat) -> Nat:
  step.go(s, b, c, m, dec(b, s))

def run(cs: List<&2, Nat>, s: Nat, +b: Nat, +m: Nat) -> Nat:
  match cs:
    case Nil{}:
      s
    case Con{c, t}:
      run(t, step(s, b, c, m), b, m)

# --- laws
law bounded:
  for b: Nat
  for m: Nat
  for cs: List<&2, Nat>
  LE(run(cs, 0n, b, m), Nat.add(b, m))

# --- proofs
def le_refl(a: Nat) -> LE(a, a):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      le_refl(x)

def le_succ(a: Nat, b: Nat, e: LE(a, b)) -> LE(a, 1n+b):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(LE(x, 0n), e)
        case 1n+y:
          le_succ(x, y, e)

def le_trans(a: Nat, b: Nat, c: Nat, ab: LE(a, b), bc: LE(b, c)) -> LE(a, c):
  match a:
    case 0n:
      Unit{}
    case 1n+x:
      match b:
        case 0n:
          Empty.absurd(LE(1n+x, c), ab)
        case 1n+y:
          match c:
            case 0n:
              Empty.absurd(LE(1n+x, 0n), bc)
            case 1n+z:
              le_trans(x, y, z, ab, bc)

def le_pred(s: Nat, b: Nat, e: LE(1n+s, b)) -> LE(s, b):
  match s b:
    case 0n y:
      Unit{}
    case 1n+x 0n:
      Empty.absurd(LE(1n+x, 0n), e)
    case 1n+x 1n+y:
      le_pred(x, y, e)

def le_add(k: Nat, +m: Nat) -> LE(m, Nat.add(k, m)):
  match k:
    case 0n:
      le_refl(m)
    case 1n++p:
      le_succ(m, Nat.add(p, m), le_add(p, m))

def add_le_l(s: Nat, -k: Nat, -j: Nat, e: LE(k, j)) -> LE(Nat.add(s, k), Nat.add(s, j)):
  match s:
    case 0n:
      e
    case 1n+p:
      add_le_l(p, k, j, e)

def add_le_r(a: Nat, b: Nat, +m: Nat, e: LE(a, b)) -> LE(Nat.add(a, m), Nat.add(b, m)):
  match a b:
    case 0n y:
      le_add(y, m)
    case 1n+x 0n:
      Empty.absurd(LE(Nat.add(1n+x, m), m), e)
    case 1n+x 1n+y:
      add_le_r(x, y, m, e)

def min_le(c: Nat, m: Nat) -> LE(Nat.min(c, m), m):
  match c m:
    case 0n y:
      Unit{}
    case 1n+x 0n:
      Unit{}
    case 1n+x 1n+y:
      min_le(x, y)

def step_ok.go(+s: Nat, +b: Nat, +c: Nat, +m: Nat, w: Cmp2<b, s>, h: LE(s, Nat.add(b, m))) -> LE(step.go(s, b, c, m, w), Nat.add(b, m)):
  match w:
    case IsLe{e}:
      h
    case IsGt{e}:
      le_trans(Nat.add(s, Nat.min(c, m)), Nat.add(s, m), Nat.add(b, m),
        add_le_l(s, Nat.min(c, m), m, min_le(c, m)),
        add_le_r(s, b, m, le_pred(s, b, e)))

def step_ok(+s: Nat, +b: Nat, +c: Nat, +m: Nat, h: LE(s, Nat.add(b, m))) -> LE(step(s, b, c, m), Nat.add(b, m)):
  step_ok.go(s, b, c, m, dec(b, s), h)

def run_ok(cs: List<&2, Nat>, +s: Nat, +b: Nat, +m: Nat, h: LE(s, Nat.add(b, m))) -> LE(run(cs, s, b, m), Nat.add(b, m)):
  match cs:
    case Nil{}:
      h
    case Con{+c, t}:
      run_ok(t, step(s, b, c, m), b, m, step_ok(s, b, c, m, h))

def bounded(b, m, cs):
  run_ok(cs, 0n, b, m, Unit{})

# --- run
def main() -> Nat:
  run([3n, 9n, 1n, 7n, 2n], 0n, 10n, 4n)
