# Rule 3, the sliding-window limit, in Bend 2: the state is the log of
# requests (forced, t); a request is admitted iff not forced and seen + 1 <= c,
# seen counting the logged requests with t < e.t + w; forced requests always go
# through; both are logged. Law: at every now, the unforced (so admitted)
# logged requests in the window ending at now (e.t <= now < e.t + w) number at
# most c, after any list of requests. Proven by hand: induction on the list,
# and a lemma that at t <= now every record ours counts is one seen counts.
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

# 1 when y < x, else 0, read off a comparison's evidence
def gt1(-x: Nat, -y: Nat, w: Cmp2<x, y>) -> Nat:
  match w:
    case IsLe{e}:
      0n
    case IsGt{e}:
      1n

# --- rule
type Ent is Data:
  MkEnt{forced: Bool, t: Nat}

# the logged requests with t < e.t + w
def seen(l: List<&2, Ent>, +t: Nat, +w: Nat) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{h, r}:
      match h:
        case MkEnt{f, +et}:
          Nat.add(gt1(Nat.add(et, w), t, dec(Nat.add(et, w), t)), seen(r, t, w))

def step.adm(+t: Nat, +l: List<&2, Ent>, -w: Nat, -c: Nat, v: Cmp2<1n+seen(l, t, w), c>) -> List<&2, Ent>:
  match v:
    case IsLe{e}:
      MkEnt{False{}, t} <> l
    case IsGt{e}:
      l

def step.go(f: Bool, +t: Nat, +l: List<&2, Ent>, +w: Nat, +c: Nat) -> List<&2, Ent>:
  match f:
    case True{}:
      MkEnt{True{}, t} <> l
    case False{}:
      step.adm(t, l, w, c, dec(1n+seen(l, t, w), c))

def step(r: Ent, +l: List<&2, Ent>, +w: Nat, +c: Nat) -> List<&2, Ent>:
  match r:
    case MkEnt{f, t}:
      step.go(f, t, l, w, c)

def run(rs: List<&2, Ent>, l: List<&2, Ent>, +w: Nat, +c: Nat) -> List<&2, Ent>:
  match rs:
    case Nil{}:
      l
    case Con{r, t}:
      run(t, step(r, l, w, c), w, c)

# --- laws
# 1 when a record is unforced and et <= now < et + w
def ours1.in(+et: Nat, +now: Nat, +w: Nat, v: Cmp2<et, now>) -> Nat:
  match v:
    case IsGt{e}:
      0n
    case IsLe{e}:
      gt1(Nat.add(et, w), now, dec(Nat.add(et, w), now))

def ours1(f: Bool, +et: Nat, +now: Nat, +w: Nat) -> Nat:
  match f:
    case True{}:
      0n
    case False{}:
      ours1.in(et, now, w, dec(et, now))

# the admitted, unforced requests in the window ending at now
def ours(l: List<&2, Ent>, +now: Nat, +w: Nat) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{h, r}:
      match h:
        case MkEnt{f, +et}:
          Nat.add(ours1(f, et, now, w), ours(r, now, w))

law ceiling:
  for w: Nat
  for c: Nat
  for now: Nat
  for rs: List<&2, Ent>
  LE(ours(run(rs, Nil{}, w, c), now, w), c)

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

def le_add(k: Nat, +m: Nat) -> LE(m, Nat.add(k, m)):
  match k:
    case 0n:
      le_refl(m)
    case 1n++p:
      le_succ(m, Nat.add(p, m), le_add(p, m))

def add_le2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, e1: LE(a, b), e2: LE(c, d)) -> LE(Nat.add(a, c), Nat.add(b, d)):
  match a b:
    case 0n y:
      le_trans(c, d, Nat.add(y, d), e2, le_add(y, d))
    case 1n+x 0n:
      Empty.absurd(LE(Nat.add(1n+x, c), d), e1)
    case 1n+x 1n+y:
      add_le2(x, y, c, d, e1, e2)

def no_succ_le(n: Nat, e: LE(1n+n, n)) -> Empty:
  match n:
    case 0n:
      e
    case 1n+p:
      no_succ_le(p, e)

# one record: if ours counts it at now, seen counts it at t <= now
def one_le.win(+et: Nat, +t: Nat, +now: Nat, +w: Nat, h: LE(t, now), u: Cmp2<Nat.add(et, w), now>, s: Cmp2<Nat.add(et, w), t>) -> LE(gt1(Nat.add(et, w), now, u), gt1(Nat.add(et, w), t, s)):
  match u:
    case IsLe{e}:
      Unit{}
    case IsGt{e}:
      match s:
        case IsGt{e2}:
          Unit{}
        case IsLe{e2}:
          no_succ_le(now, le_trans(1n+now, Nat.add(et, w), now, e, le_trans(Nat.add(et, w), t, now, e2, h)))

def one_le.in(+et: Nat, +t: Nat, +now: Nat, +w: Nat, h: LE(t, now), v: Cmp2<et, now>) -> LE(ours1.in(et, now, w, v), gt1(Nat.add(et, w), t, dec(Nat.add(et, w), t))):
  match v:
    case IsGt{e}:
      Unit{}
    case IsLe{e}:
      one_le.win(et, t, now, w, h, dec(Nat.add(et, w), now), dec(Nat.add(et, w), t))

def one_le(f: Bool, +et: Nat, +t: Nat, +now: Nat, +w: Nat, h: LE(t, now)) -> LE(ours1(f, et, now, w), gt1(Nat.add(et, w), t, dec(Nat.add(et, w), t))):
  match f:
    case True{}:
      Unit{}
    case False{}:
      one_le.in(et, t, now, w, h, dec(et, now))

# at t <= now, ours <= seen
def le_seen(l: List<&2, Ent>, +t: Nat, +now: Nat, +w: Nat, +h: LE(t, now)) -> LE(ours(l, now, w), seen(l, t, w)):
  match l:
    case Nil{}:
      Unit{}
    case Con{x, +r}:
      match x:
        case MkEnt{+f, +et}:
          add_le2(ours1(f, et, now, w), gt1(Nat.add(et, w), t, dec(Nat.add(et, w), t)), ours(r, now, w), seen(r, t, w),
            one_le(f, et, t, now, w, h), le_seen(r, t, now, w, h))

def step_ok.win(+t: Nat, +l: List<&2, Ent>, +w: Nat, +c: Nat, +now: Nat, h: LE(ours(l, now, w), c), e: LE(1n+seen(l, t, w), c), x: LE(t, now), u: Cmp2<Nat.add(t, w), now>) -> LE(Nat.add(gt1(Nat.add(t, w), now, u), ours(l, now, w)), c):
  match u:
    case IsLe{y}:
      h
    case IsGt{y}:
      le_trans(1n+ours(l, now, w), 1n+seen(l, t, w), c, le_seen(l, t, now, w, x), e)

def step_ok.in(+t: Nat, +l: List<&2, Ent>, +w: Nat, +c: Nat, +now: Nat, h: LE(ours(l, now, w), c), e: LE(1n+seen(l, t, w), c), v: Cmp2<t, now>) -> LE(Nat.add(ours1.in(t, now, w, v), ours(l, now, w)), c):
  match v:
    case IsGt{x}:
      h
    case IsLe{x}:
      step_ok.win(t, l, w, c, now, h, e, x, dec(Nat.add(t, w), now))

def step_ok.adm(+t: Nat, +l: List<&2, Ent>, +w: Nat, +c: Nat, +now: Nat, h: LE(ours(l, now, w), c), v: Cmp2<1n+seen(l, t, w), c>) -> LE(ours(step.adm(t, l, w, c, v), now, w), c):
  match v:
    case IsGt{e}:
      h
    case IsLe{e}:
      step_ok.in(t, l, w, c, now, h, e, dec(t, now))

def step_ok.go(f: Bool, +t: Nat, +l: List<&2, Ent>, +w: Nat, +c: Nat, +now: Nat, h: LE(ours(l, now, w), c)) -> LE(ours(step.go(f, t, l, w, c), now, w), c):
  match f:
    case True{}:
      h
    case False{}:
      step_ok.adm(t, l, w, c, now, h, dec(1n+seen(l, t, w), c))

def step_ok(r: Ent, +l: List<&2, Ent>, +w: Nat, +c: Nat, +now: Nat, h: LE(ours(l, now, w), c)) -> LE(ours(step(r, l, w, c), now, w), c):
  match r:
    case MkEnt{f, t}:
      step_ok.go(f, t, l, w, c, now, h)

def run_ok(rs: List<&2, Ent>, +l: List<&2, Ent>, +w: Nat, +c: Nat, +now: Nat, h: LE(ours(l, now, w), c)) -> LE(ours(run(rs, l, w, c), now, w), c):
  match rs:
    case Nil{}:
      h
    case Con{+r, t}:
      run_ok(t, step(r, l, w, c), w, c, now, step_ok(r, l, w, c, now, h))

def ceiling(w, c, now, rs):
  run_ok(rs, Nil{}, w, c, now, Unit{})

# --- run
# The bench (compare/bench): N requests from the LCG x' = (x * 1103515245 +
# 12345) mod 2^31, x from 42, each request's t = the previous t + x mod 3 (from
# 0), forced = x mod 10 == 0; w = 60, c = 5. Prints the number of logged
# requests, how many of them were forced, and the sum of their t.
def lcg(x: U32) -> U32:
  ((x * 1103515245 + 12345) .&. 2147483647 : U32)

def gen(n: Nat, x: U32, +t: Nat) -> List<&2, Ent>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +y = lcg(x)
      +u = Nat.add(t, U32.to_nat((y % 3 : U32)))
      MkEnt{U32.is_eq((y % 10 : U32), 0), u} <> gen(p, y, u)

def forced1(f: Bool) -> Nat:
  match f:
    case True{}:
      1n
    case False{}:
      0n

def sums(l: List<&2, Ent>, n: Nat, f: Nat, s: Nat) -> String:
  match l:
    case Nil{}:
      Nat.show(n) ++ " " ++ Nat.show(f) ++ " " ++ Nat.show(s)
    case Con{h, r}:
      match h:
        case MkEnt{x, t}:
          sums(r, 1n+n, Nat.add(f, forced1(x)), Nat.add(s, t))

def bench(+n: Nat) -> String:
  sums(run(gen(n, 42, 0n), Nil{}, 60n, 5n), 0n, 0n, 0n)

def arg.read(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case Some{n}:
      n
    case None{}:
      0n

def arg(xs: List<String>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{p, t}:
      match t:
        case Nil{}:
          0n
        case Con{s, r}:
          arg.read(Nat.read(s))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    IO.print(bench(arg(xs)))
