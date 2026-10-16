# Rule 2, per-key caps, in Bend 2: the state is the list of grants (acct,
# day); a request is granted iff ok and its account has no grant yet and its
# day has fewer than d. Laws: at every key k, at most one grant per account
# and at most d per day, after any list of requests. Proven by hand: the key
# is fixed and the induction runs over the list; the comparisons the step
# makes, and the key tests the counts make, carry their evidence.
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

# a key test with its evidence
type Same<-a: Nat, -k: Nat> is Data:
  Hit{e: {a == k : Nat}}
  Miss{}

def same.up(-x: Nat, -y: Nat, w: Same<x, y>) -> Same<1n+x, 1n+y>:
  match w:
    case Hit{e}:
      Hit{Equal.cong(Nat, Nat, n => 1n+n, x, y, e)}
    case Miss{}:
      Miss{}

def same(a: Nat, k: Nat) -> Same<a, k>:
  match a k:
    case 0n 0n:
      Hit{{==}}
    case 0n 1n+y:
      Miss{}
    case 1n+x 0n:
      Miss{}
    case 1n+x 1n+y:
      same.up(x, y, same(x, y))

def hit(-a: Nat, -k: Nat, w: Same<a, k>) -> Nat:
  match w:
    case Hit{e}:
      1n
    case Miss{}:
      0n

# --- rule
type Req is Data:
  MkReq{ok: Bool, acct: Nat, day: Nat}

type Grant is Data:
  MkGrant{acct: Nat, day: Nat}

def count_acct(g: List<&2, Grant>, +k: Nat) -> Nat:
  match g:
    case Nil{}:
      0n
    case Con{h, t}:
      match h:
        case MkGrant{+a, y}:
          Nat.add(hit(a, k, same(a, k)), count_acct(t, k))

def count_day(g: List<&2, Grant>, +k: Nat) -> Nat:
  match g:
    case Nil{}:
      0n
    case Con{h, t}:
      match h:
        case MkGrant{a, +y}:
          Nat.add(hit(y, k, same(y, k)), count_day(t, k))

def step.day(acct: Nat, +day: Nat, +g: List<&2, Grant>, -d: Nat, w: Cmp2<d, count_day(g, day)>) -> List<&2, Grant>:
  match w:
    case IsLe{e}:
      g
    case IsGt{e}:
      MkGrant{acct, day} <> g

def step.acct(+acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, w: Cmp2<1n, count_acct(g, acct)>) -> List<&2, Grant>:
  match w:
    case IsLe{e}:
      g
    case IsGt{e}:
      step.day(acct, day, g, d, dec(d, count_day(g, day)))

def step.ok(ok: Bool, +acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat) -> List<&2, Grant>:
  match ok:
    case False{}:
      g
    case True{}:
      step.acct(acct, day, g, d, dec(1n, count_acct(g, acct)))

def step(r: Req, +g: List<&2, Grant>, +d: Nat) -> List<&2, Grant>:
  match r:
    case MkReq{ok, acct, day}:
      step.ok(ok, acct, day, g, d)

def run(rs: List<&2, Req>, g: List<&2, Grant>, +d: Nat) -> List<&2, Grant>:
  match rs:
    case Nil{}:
      g
    case Con{r, t}:
      run(t, step(r, g, d), d)

# --- laws
law once_per_acct:
  for d: Nat
  for rs: List<&2, Req>
  for k: Nat
  LE(count_acct(run(rs, Nil{}, d), k), 1n)

law day_cap:
  for d: Nat
  for rs: List<&2, Req>
  for k: Nat
  LE(count_day(run(rs, Nil{}, d), k), d)

# --- proofs
# once per account: a grant at key k needs count_acct(g, k) = 0
def acct_ok.hit(+acct: Nat, +g: List<&2, Grant>, +k: Nat, ea: LE(1n+count_acct(g, acct), 1n), w: Same<acct, k>, h: LE(count_acct(g, k), 1n)) -> LE(Nat.add(hit(acct, k, w), count_acct(g, k)), 1n):
  match w:
    case Hit{e}:
      %e : LE(1n+count_acct(g, _), 1n)
      ea
    case Miss{}:
      h

def acct_ok.day(+acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, ea: LE(1n+count_acct(g, acct), 1n), w: Cmp2<d, count_day(g, day)>, h: LE(count_acct(g, k), 1n)) -> LE(count_acct(step.day(acct, day, g, d, w), k), 1n):
  match w:
    case IsLe{e}:
      h
    case IsGt{e}:
      acct_ok.hit(acct, g, k, ea, same(acct, k), h)

def acct_ok.acct(+acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, w: Cmp2<1n, count_acct(g, acct)>, h: LE(count_acct(g, k), 1n)) -> LE(count_acct(step.acct(acct, day, g, d, w), k), 1n):
  match w:
    case IsLe{e}:
      h
    case IsGt{e}:
      acct_ok.day(acct, day, g, d, k, e, dec(d, count_day(g, day)), h)

def acct_ok.ok(ok: Bool, +acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, h: LE(count_acct(g, k), 1n)) -> LE(count_acct(step.ok(ok, acct, day, g, d), k), 1n):
  match ok:
    case False{}:
      h
    case True{}:
      acct_ok.acct(acct, day, g, d, k, dec(1n, count_acct(g, acct)), h)

def acct_ok(r: Req, +g: List<&2, Grant>, +d: Nat, +k: Nat, h: LE(count_acct(g, k), 1n)) -> LE(count_acct(step(r, g, d), k), 1n):
  match r:
    case MkReq{ok, acct, day}:
      acct_ok.ok(ok, acct, day, g, d, k, h)

def acct_run(rs: List<&2, Req>, +g: List<&2, Grant>, +d: Nat, +k: Nat, h: LE(count_acct(g, k), 1n)) -> LE(count_acct(run(rs, g, d), k), 1n):
  match rs:
    case Nil{}:
      h
    case Con{+r, t}:
      acct_run(t, step(r, g, d), d, k, acct_ok(r, g, d, k, h))

def once_per_acct(d, rs, k):
  acct_run(rs, Nil{}, d, k, Unit{})

# day cap: a grant at key k needs count_day(g, k) < d
def day_ok.hit(+day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, ed: LE(1n+count_day(g, day), d), w: Same<day, k>, h: LE(count_day(g, k), d)) -> LE(Nat.add(hit(day, k, w), count_day(g, k)), d):
  match w:
    case Hit{e}:
      %e : LE(1n+count_day(g, _), d)
      ed
    case Miss{}:
      h

def day_ok.day(+acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, w: Cmp2<d, count_day(g, day)>, h: LE(count_day(g, k), d)) -> LE(count_day(step.day(acct, day, g, d, w), k), d):
  match w:
    case IsLe{e}:
      h
    case IsGt{e}:
      day_ok.hit(day, g, d, k, e, same(day, k), h)

def day_ok.acct(+acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, w: Cmp2<1n, count_acct(g, acct)>, h: LE(count_day(g, k), d)) -> LE(count_day(step.acct(acct, day, g, d, w), k), d):
  match w:
    case IsLe{e}:
      h
    case IsGt{e}:
      day_ok.day(acct, day, g, d, k, dec(d, count_day(g, day)), h)

def day_ok.ok(ok: Bool, +acct: Nat, +day: Nat, +g: List<&2, Grant>, +d: Nat, +k: Nat, h: LE(count_day(g, k), d)) -> LE(count_day(step.ok(ok, acct, day, g, d), k), d):
  match ok:
    case False{}:
      h
    case True{}:
      day_ok.acct(acct, day, g, d, k, dec(1n, count_acct(g, acct)), h)

def day_ok(r: Req, +g: List<&2, Grant>, +d: Nat, +k: Nat, h: LE(count_day(g, k), d)) -> LE(count_day(step(r, g, d), k), d):
  match r:
    case MkReq{ok, acct, day}:
      day_ok.ok(ok, acct, day, g, d, k, h)

def day_run(rs: List<&2, Req>, +g: List<&2, Grant>, +d: Nat, +k: Nat, h: LE(count_day(g, k), d)) -> LE(count_day(run(rs, g, d), k), d):
  match rs:
    case Nil{}:
      h
    case Con{+r, t}:
      day_run(t, step(r, g, d), d, k, day_ok(r, g, d, k, h))

def day_cap(d, rs, k):
  day_run(rs, Nil{}, d, k, Unit{})

# --- run
def main() -> List<&2, Grant>:
  run([MkReq{True{}, 1n, 5n}, MkReq{True{}, 1n, 5n}, MkReq{True{}, 2n, 5n}, MkReq{True{}, 3n, 5n}, MkReq{False{}, 4n, 6n}], Nil{}, 2n)
