"""An SV-COMP termination task's C program as an ARI integer transition system:

    python3 c2ari.py task.c [--yml task.yml] [--data-model LP64|ILP32] [--no-overflow] [--for terminates|nonterminating]

Refused (exit 2, the reason on stderr as one JSON line) where the program leaves the subset below. `--yml` reads the
task's data model and whether it declares no signed overflow (no-overflow.prp expected true); without it, LP64 and
none declared. A program with recursion needs `--for` (below); any other has one translation, the same for both.

The subset: main and the functions it calls, each call inlined (its parameters fresh variables set to the arguments,
converted to their types, its body over the globals and them; a call inside an expression is evaluated before the rest
of it, into a fresh variable), over C's integer types (_Bool, char, short, int, long, long long, signed and unsigned,
enums; locals and globals), arrays of a fixed size, and pointers to a fixed set of objects; assignments, ++/--,
compound assignments, if, while, do-while, for, break, continue, return, goto and labels; expressions with + - *
(products of variables too), / and % (C's truncation toward zero: the quotient a fresh value q with the remainder
x − d·q between 0 and d, its sign x's), comparisons, && || !, ~, the ternary operator and a condition used as a value,
casts; __VERIFIER_nondet_<type>() anywhere an expression may be (a fresh value in the type's range),
__VERIFIER_assume(c) (the run goes on only where c holds), and abort(), exit(), reach_error(), __VERIFIER_error() (the
run ends) where the task doesn't define them (a task's own reach_error is its own function, unless its body is just a
call to an end it doesn't define). The program's locations are the system's; a run is the program's execution: every
variable starts as C starts it (a global or a static local in main at its initializer or 0, a local at any value of its
type: reading it before it is written is indeterminate, so any value is what the task can do), and the entry's own
values are overwritten on the first step. The preprocessor: lines spliced and comments left out as C's phases 2 and 3
do; #include of stdlib.h, stdio.h, assert.h or stdbool.h and line markers left out; any other directive refused.

The values, exactly C's (the SV-COMP data model: LP64 or ILP32, char signed, two's complement): every value is an
integer in its type's range. An unsigned operation's result is taken modulo 2^n (a fresh k with r − 2^n·k in
[0, 2^n)); C's conversions are made where C makes them (the integer promotions, the usual arithmetic conversions, on
assignment, argument, return and cast): to an unsigned type modulo 2^n; to a narrower signed type modulo 2^n into its
range (implementation-defined; gcc's, which every SV-COMP platform uses); to _Bool, 0 or 1 (any nonzero value is 1).
An enum's type is gcc's: unsigned int where none of its constants is negative, else int (its constants are ints); a
task's typedef of bool is its own type, stdbool's bool is _Bool.

Undefined behaviour ends the run: a signed operation whose result is out of its type's range (unless the task
declares none can be: then no run has one and nothing is checked), a division by zero, an access out of an array's
bounds, through a null, freed, too small or indeterminate pointer, or the use of an indeterminate pointer. The run is
cut there (no rule fires), which is how SV-COMP's verdicts read it: cohencu1-both-t is expected to terminate though
its loop test 6·n + 6 <= k overflows at k = INT_MAX (wrapped, the test would hold forever), and Binomial,
TerminatorRec02 and RecursiveMultiplication-1, whose products overflow, are expected to terminate. So "terminates"
means every run ends or reaches undefined behaviour, and "nonterminating" an infinite run without any.

Pointers: a pointer is the number of the object it points to (0 null, -1 indeterminate); the objects are the globals
and main's outermost locals whose address is taken (&x, alive for the whole run), and the cells of malloc, calloc and
alloca calls in main or in functions it calls, each executed at most once (no loop or goto around it, no recursion):
malloc may return null; free makes its cell dead. *p is the object p points to (each object a case of the rule);
pointers are copied, compared for equality and with 0, passed and returned; every pointer read through has one
pointee type; no pointer arithmetic. Arrays of n elements: an element per variable, an access at an index that is not
a constant one case per element; past 64 elements, only the elements read at a constant index (int constants under
+ - *, no names) are kept (an array read at any other index is refused), a write elsewhere in the bounds changing
nothing read.

Recursion (a cycle of calls among the functions main reaches): a call to a function already being inlined L deep is a
boundary, and the two translations differ there; each is exact for its one answer and the other is not read from it:
  --for terminates: L = 0 (every call to a recursive function is a boundary). At a boundary the run either goes into
    the function's own copy (its parameters set, the caller's frame forgotten: a call that never returns), or skips
    the call, the result any value of the return type and every global the function may write any value of its type
    (a call that returns). Every infinite run of the program is one of the system's: either its depth grows forever
    (each frame forgotten at the call that never returns) or some frame is never left after some point, every call it
    makes after that returning. A return out of a function's own copy ends the run. So the system's termination is
    the program's (the system has more runs).
  --for nonterminating: L as deep as the system stays small (at most 4). At a boundary the run goes into the
    function's own copy only, a return out of it ending the run: every run of the system is a run of the program up
    to there (entering a call and running on inside it), so an infinite one is the program's.

`--unchecked`: no signed operation is checked for overflow (arithmetic on unbounded integers past it). Every run of
the program is then a prefix of one of the system's (the same until its undefined behaviour, where the program's run
ends), so the system's termination is the program's: a translation for "terminates" only, beside the checked one.

What the translation changes, said once here: nothing past what the recursion and --unchecked translations say.

Refused, by reason, the data first (prescan): structs, floats, pointers to pointers, function pointers, pointer
arithmetic; then the code: calls to functions with no body (but the ones above); a call in a conditional part of an
expression (after && or ||, in a ternary's branch); where C leaves an expression's order unspecified and it can matter:
two calls in one expression, one of which may write a global or through a pointer or end the run (but a call inside
another's arguments, which comes first); a call that may write a global the rest of the expression reads (an
assignment's target included: g += f(), a[g] = f()), or that may write through a pointer in an expression that reads
any variable (x + set(&x), pick(x, set(&x))); bitwise and, or, xor and shifts; switch; static locals outside main's
outermost block, or with goto.
"""
import json
import re
import sys

from pycparser import c_ast, c_parser


class Refused(Exception):
    pass


# --- types --------------------------------------------------------------------------------------------------------------
# An integer type: ('i', signed, bits, rank); rank orders the integer conversion ranks (_Bool 0, char 1, short 2, int 3,
# long 4, long long 5). A pointer: ('p', pointee). An array: ('a', element, n). void: ('v',).
DM = {"long": 64, "ptr": 64}


def ity(signed, bits, rank):
    return ("i", signed, bits, rank)


BOOL = ity(False, 1, 0)
INT = ity(True, 32, 3)
VOID = ("v",)


def LONG(signed=True):
    return ity(signed, DM["long"], 4)


def rng(t):
    if t == BOOL:
        return (0, 1)
    _, s, b, _ = t
    return (-(2 ** (b - 1)), 2 ** (b - 1) - 1) if s else (0, 2 ** b - 1)


def promote(t):
    return INT if t[3] < 3 else t


def usual(a, b):
    """C's usual arithmetic conversions, on promoted types."""
    a, b = promote(a), promote(b)
    if a == b:
        return a
    if a[1] == b[1]:
        return a if a[3] >= b[3] else b
    u, s = (a, b) if not a[1] else (b, a)
    if u[3] >= s[3]:
        return u
    if s[2] > u[2]:
        return s
    return ity(False, s[2], s[3])


def within(a, b):
    """Every value of a is one of b."""
    la, ha = rng(a)
    lb, hb = rng(b)
    return lb <= la and ha <= hb


def sizeof(t):
    if t[0] == "p":
        return DM["ptr"] // 8
    if t[0] == "a":
        return t[2] * sizeof(t[1])
    if t[0] == "i":
        return 1 if t[2] <= 8 else t[2] // 8
    raise Refused("sizeof")


def base_type(names):
    """An integer type from a list of specifiers."""
    n = [x for x in names if x not in ("const", "volatile", "signed", "unsigned", "register", "auto", "extern")]
    unsigned = "unsigned" in names
    if "float" in names or "double" in names:
        raise Refused("floats")
    if len(n) == 1 and n[0] in TYPEDEFS:  # (a task's own bool, typedef'd as an enum, before stdbool's)
        t = TYPEDEFS[n[0]]
        if isinstance(t, Refused):
            raise t
        return t
    if n == ["_Bool"] or n == ["bool"]:
        return BOOL
    if n == ["char"]:
        return ity(not unsigned, 8, 1)
    if n in (["short"], ["short", "int"]):
        return ity(not unsigned, 16, 2)
    if n in ([], ["int"]):
        return ity(not unsigned, 32, 3)
    if n in (["long"], ["long", "int"]):
        return ity(not unsigned, DM["long"], 4)
    if n in (["long", "long"], ["long", "long", "int"]):
        return ity(not unsigned, 64, 5)
    if n == ["void"]:
        return VOID
    if len(n) == 1 and n[0] in TYPEDEFS:
        t = TYPEDEFS[n[0]]
        if isinstance(t, Refused):
            raise t
        return t
    raise Refused(f"the type {' '.join(names)}")


def type_of(t):
    """The type of a declaration's type node."""
    if isinstance(t, c_ast.TypeDecl):
        return type_of(t.type)
    if isinstance(t, c_ast.Typename):
        return type_of(t.type)
    if isinstance(t, c_ast.PtrDecl):
        inner = type_of(t.type)
        if inner[0] == "p":
            raise Refused("pointers to pointers")
        if inner[0] == "a":
            raise Refused("pointers to arrays")
        return ("p", inner)
    if isinstance(t, c_ast.ArrayDecl):
        el = type_of(t.type)
        if el[0] != "i":
            raise Refused("arrays of arrays or of pointers")
        if t.dim is None:
            raise Refused("an array of no fixed size")
        n = const_expr(t.dim)
        if n is None or n <= 0:
            raise Refused("an array of no fixed size")
        return ("a", el, n)
    if isinstance(t, (c_ast.Struct, c_ast.Union)):
        raise Refused("structs")
    if isinstance(t, c_ast.Enum):
        return enum_type(t)
    if isinstance(t, c_ast.FuncDecl):
        raise Refused("function pointers")
    if isinstance(t, c_ast.IdentifierType):
        return base_type(t.names)
    raise Refused(f"the type {type(t).__name__}")


TYPEDEFS = {}
ENUMS = {}
ENUM_TAGS = {}


def enum_type(t):
    """An enum's type, gcc's (C11 6.7.2.2p4 leaves it to the implementation): unsigned int where no constant is
    negative, else int; its constants (each an int, the one before it + 1 where it has no value) recorded."""
    if t.values is None:
        if t.name in ENUM_TAGS:
            return ENUM_TAGS[t.name]
        raise Refused("an enum declared nowhere")
    v, vals = -1, []
    for e in t.values.enumerators:
        if e.value is None:
            v = v + 1
        else:
            c = const_expr(e.value)
            if c is None:
                raise Refused("an enum value that isn't a constant")
            v = c
        if not rng(INT)[0] <= v <= rng(INT)[1]:
            raise Refused("an enum constant past int's range")
        ENUMS[e.name] = v
        vals.append(v)
    ty = INT if any(x < 0 for x in vals) else ity(False, 32, 3)
    if t.name:
        ENUM_TAGS[t.name] = ty
    return ty


def const_expr(e):
    """An integer constant expression's value (array sizes, enum values), or None."""
    if isinstance(e, c_ast.Constant):
        try:
            return constant(e)[0]
        except Refused:
            return None
    if isinstance(e, c_ast.ID) and e.name in ENUMS:
        return ENUMS[e.name]
    if isinstance(e, c_ast.UnaryOp) and e.op in ("-", "+"):
        v = const_expr(e.expr)
        return None if v is None else (-v if e.op == "-" else v)
    if isinstance(e, c_ast.UnaryOp) and e.op == "sizeof" and isinstance(e.expr, c_ast.Typename):
        return sizeof(type_of(e.expr))
    if isinstance(e, c_ast.BinaryOp) and e.op in ("+", "-", "*"):
        a, b = const_expr(e.left), const_expr(e.right)
        if a is None or b is None:
            return None
        return a + b if e.op == "+" else a - b if e.op == "-" else a * b
    return None


ESC = {"n": 10, "t": 9, "r": 13, "0": 0, "\\": 92, "'": 39, '"': 34, "a": 7, "b": 8, "f": 12, "v": 11}


def constant(e):
    """An integer constant's value and type (C11 6.4.4.1), a character constant's (int)."""
    if e.type == "char":
        s = e.value[1:-1]
        if s.startswith("\\x"):
            v = int(s[2:], 16)
        elif s.startswith("\\") and s[1:].isdigit():
            v = int(s[1:], 8)
        elif s.startswith("\\"):
            if s[1:] not in ESC:
                raise Refused(f"the character constant {e.value}")
            v = ESC[s[1:]]
        elif len(s) == 1:
            v = ord(s)
        else:
            raise Refused(f"the character constant {e.value}")
        return (v - 256 if v > 127 else v), INT
    if not (e.type in ("int", "long int", "long long int") or e.type.startswith(("int", "long", "unsigned"))):
        raise Refused(f"a constant of type {e.type}" if "double" not in e.type and "float" not in e.type else "floats")
    m = re.fullmatch(r"(0[xX][0-9a-fA-F]+|0[0-7]*|[1-9][0-9]*)([uUlL]*)", e.value)
    if not m:
        raise Refused(f"the constant {e.value}")
    digits, suf = m.group(1), m.group(2).lower()
    v = int(digits, 16) if digits[:2].lower() == "0x" else int(digits, 8) if digits.startswith("0") and len(digits) > 1 else int(digits)
    dec = not (digits.startswith("0") and len(digits) > 1)
    L, LL = DM["long"], 64
    u = "u" in suf
    nl = suf.count("l")
    cands = []
    if nl == 0:
        cands = [ity(True, 32, 3), ity(False, 32, 3)] if not u else [ity(False, 32, 3)]
    if nl <= 1:
        cands += [ity(True, L, 4), ity(False, L, 4)] if not u else [ity(False, L, 4)]
    cands += [ity(True, LL, 5), ity(False, LL, 5)] if not u else [ity(False, LL, 5)]
    if dec and not u:
        cands = [c for c in cands if c[1]]
    for c in cands:
        if rng(c)[0] <= v <= rng(c)[1]:
            return v, c
    raise Refused(f"the constant {e.value} (no type holds it)")


# --- conditions ---------------------------------------------------------------------------------------------------------
# A condition's negation, pushed to the comparisons (KoAT2's ARI reader takes no `not` and no `distinct`).
FLIP = {"<": ">=", "<=": ">", ">": "<=", ">=": "<"}


def neg(c):
    if c == "true":
        return "false"
    if c == "false":
        return "true"
    op = c[0]
    if op == "and":
        return ["or", *[neg(x) for x in c[1:]]]
    if op == "or":
        return ["and", *[neg(x) for x in c[1:]]]
    if op == "=":
        return ["or", ["<", c[1], c[2]], [">", c[1], c[2]]]
    return [FLIP[op], c[1], c[2]]


def simp(c):
    """true and false folded away (KoAT2's ARI reader takes neither)."""
    if isinstance(c, str) or c[0] not in ("and", "or"):
        return c
    xs = [simp(x) for x in c[1:]]
    unit, zero = ("true", "false") if c[0] == "and" else ("false", "true")
    if zero in xs:
        return zero
    xs = [x for x in xs if x != unit]
    return unit if not xs else xs[0] if len(xs) == 1 else [c[0], *xs]


def num(v):
    return str(v) if v >= 0 else ["-", str(-v)]


def cval(s):
    """The value of a term over constants, or None."""
    if isinstance(s, str):
        return int(s) if s.isdigit() else None
    if s[0] == "-" and len(s) == 2:
        v = cval(s[1])
        return None if v is None else -v
    if s[0] in ("+", "-", "*") and len(s) == 3:
        a, b = cval(s[1]), cval(s[2])
        if a is None or b is None:
            return None
        return a + b if s[0] == "+" else a - b if s[0] == "-" else a * b
    return None


def conj(*xs):
    return ["and", *xs] if len(xs) > 1 else xs[0]


class V:
    """A value: its term, its type and, for an unsigned value, whether the term is only its value modulo 2^n (raw)."""
    __slots__ = ("sx", "ty", "raw")

    def __init__(self, sx, ty, raw=False):
        self.sx, self.ty, self.raw = sx, ty, raw


class Program:
    def __init__(self, no_overflow):
        self.vars = []  # unique names, in slot order
        self.kinds = {}
        self.rules = []  # (from, to, guards, updates{var: sx})
        self.nlocs = 0
        self.fresh = 0
        self.features = set()
        self.labels = {}
        self.inlined = 0
        self.no_overflow = no_overflow
        self.cells = []  # the objects a pointer can name: (slot, type, alive slot or None)

    def loc(self):
        self.nlocs += 1
        return f"l{self.nlocs - 1}"

    def var(self, name, kind):
        u = f"v_{name}" if f"v_{name}" not in self.kinds else f"v_{name}_{len(self.vars)}"
        self.vars.append(u)
        self.kinds[u] = kind
        if kind[0] == "i" and (kind[2] < 32 or kind == BOOL):
            self.features.add("narrow values")
        if kind[0] == "i" and not kind[1]:
            self.features.add("unsigned")
        return u

    def new(self, prefix):
        self.fresh += 1
        return f"{prefix}_{self.fresh}"

    def nondet(self, kind, guards):
        v = self.new("nd")
        if kind[0] == "i":
            lo, hi = rng(kind)
            guards += [["<=", num(lo), v], ["<=", v, num(hi)]]
        return v

    def rule(self, a, b, guards=(), updates=None):
        self.rules.append((a, b, list(guards), dict(updates or {})))


NONDET = {"int": INT, "uint": ity(False, 32, 3), "unsigned": ity(False, 32, 3), "short": ity(True, 16, 2), "ushort": ity(False, 16, 2),
          "char": ity(True, 8, 1), "uchar": ity(False, 8, 1), "bool": BOOL, "_Bool": BOOL, "long": "long", "ulong": "ulong",
          "longlong": ity(True, 64, 5), "ulonglong": ity(False, 64, 5), "size_t": "ulong"}
ENDS = {"abort", "exit", "reach_error", "__VERIFIER_error", "__assert_fail"}
ALLOC = {"malloc", "calloc", "alloca", "__builtin_alloca"}
ASSUME = ("__VERIFIER_assume", "assume_abort_if_not")


def nondet_type(name):
    if not name or not name.startswith("__VERIFIER_nondet_"):
        return None
    k = name[len("__VERIFIER_nondet_"):]
    if k not in NONDET:
        raise Refused("floats" if k in ("float", "double") else f"the nondet function {name}")
    t = NONDET[k]
    return LONG(True) if t == "long" else LONG(False) if t == "ulong" else t


class Main:
    def __init__(self, prog, funcs, info, mode, depth):
        self.p = prog
        self.scopes = [{}]
        self.types = {}  # slot -> type (integers, pointers, arrays' element slots)
        self.arrays = {}  # array slot name -> (element type, n, {index: slot}, full)
        self.funcs = funcs  # the program's other functions, inlined at each call
        self.info = info  # per function: writes (globals), ends, recursive, allocs, loops
        self.calls = []  # the functions being inlined (a call to one of them is recursion)
        self.ret = None  # the variable a return writes, inside an inlined function
        self.ret_ty = None
        self.pend = "lend"  # where abort(), exit() and the errors go
        self.inst = 0
        self.mode = mode
        self.depth = depth
        self.tops = {}  # a recursive function's own copy: (entry, params, param types)
        self.loops = 0  # loops around the code being translated (with the inlined callers')
        self.ntemp = 0
        self.ub = 0  # guards that rule out undefined behaviour, counted (under && and || they hold only where evaluated)

    def main_top(self):
        """In main's outermost block, outside any loop: run once, alive to the end."""
        return not self.calls and len(self.scopes) == 2 and self.loops == 0

    # --- undefined behaviour and conversions ------------------------------------------------------------------------
    def signed_result(self, sx, t, g):
        """A signed operation's result: out of its type's range it is undefined behaviour, and the run ends."""
        if self.p.no_overflow:
            return V(sx, t)
        c = cval(sx)
        lo, hi = rng(t)
        if c is not None:
            if not lo <= c <= hi:
                self.ub += 1
                g.append("false")
            return V(sx, t)
        self.p.features.add("overflow checked")
        self.ub += 1
        g += [["<=", num(lo), sx], ["<=", sx, num(hi)]]
        return V(sx, t)

    def modulo(self, sx, t, g):
        """sx taken modulo 2^n into t's range (a fresh k: sx − 2^n·k in the range)."""
        lo, hi = rng(t)
        c = cval(sx)
        m = 2 ** t[2]
        if c is not None:
            return num((c - lo) % m + lo)
        k = self.p.new("k")
        r = ["-", sx, ["*", str(m), k]]
        g += [["<=", num(lo), r], ["<=", r, num(hi)]]
        return r

    def norm(self, v, g):
        if v.raw:
            return V(self.modulo(v.sx, v.ty, g), v.ty)
        return v

    def conv(self, v, to, g):
        """v converted to the integer type `to` (C 6.3.1): a term with a value in its range."""
        if to[0] != "i":
            raise Refused("an integer converted to a pointer")
        if v.ty[0] != "i":
            raise Refused("a pointer converted to an integer")
        v = self.norm(v, g)
        if to == BOOL:
            if v.ty == BOOL:
                return v.sx
            c = cval(v.sx)
            if c is not None:
                return "0" if c == 0 else "1"
            b = self.p.new("b")
            g.append(["or", ["and", ["=", v.sx, "0"], ["=", b, "0"]], ["and", ["or", ["<", v.sx, "0"], [">", v.sx, "0"]], ["=", b, "1"]]])
            return b
        if within(v.ty, to):
            return v.sx
        self.p.features.add("conversions")
        return self.modulo(v.sx, to, g)

    def as_type(self, v, t, g):
        """v as an operand of type t after the usual arithmetic conversions (raw where t is unsigned)."""
        if v.ty == t:
            return v
        if v.raw and t[2] > v.ty[2]:
            v = self.norm(v, g)
        if not t[1]:
            return V(v.sx, t, v.raw or not within(v.ty, t))
        v = self.norm(v, g)
        return V(v.sx, t)  # a signed t holds every value of v's type (6.3.1.8)

    # --- calls ------------------------------------------------------------------------------------------------------
    def callee(self, e):
        return isinstance(e, c_ast.FuncCall) and isinstance(e.name, c_ast.ID) and e.name.name in self.funcs

    def sig(self, name):
        f = self.funcs[name]
        params = [x for x in (f.decl.type.args.params if f.decl.type.args else []) if not isinstance(x, c_ast.Typename)]
        ps = [(x.name, type_of(x.type)) for x in params]
        ps = [(n, ("p", t[1]) if t[0] == "a" else t) for n, t in ps]
        for _, t in ps:
            if t[0] == "p" and t[1][0] == "a":
                raise Refused("pointers to arrays")
        return ps, type_of(f.decl.type.type)

    def args(self, call, ps, g):
        """The arguments, each converted to its parameter's type."""
        args = call.args.exprs if call.args else []
        if len(ps) != len(args):
            raise Refused(f"a call with {len(args)} arguments to {call.name.name} of {len(ps)}")
        out = []
        for (_, t), a in zip(ps, args):
            out.append(self.ptr_value(a, g) if t[0] == "p" else self.conv(self.term(a, g), t, g))
        return out

    def inline(self, call, cur, target=None, target_ty=None):
        """f(args) at `cur`, inlined: its parameters fresh variables set to the arguments, its body over the globals and
        them, each return to one location after it; `target`, the variable its value goes to."""
        p, name = self.p, call.name.name
        cur, call = self.hoist(call, cur, keep=True)
        if name in self.info["recursive"] and self.calls.count(name) >= self.depth:
            return self.boundary(call, cur, target, target_ty)
        ps, rt = self.sig(name)
        g = []
        vals = self.args(call, ps, g)
        scope, upd = {}, {}
        for (x, t), v in zip(ps, vals):
            u = p.var(x, t)
            self.types[u] = t
            scope[x] = u
            upd[u] = v
        rv = None if rt == VOID else p.var(f"ret_{name}", rt)
        if rv:
            self.types[rv] = rt
        body = p.loc()
        p.rule(cur, body, g, upd)
        saved = (self.scopes, self.ret, self.ret_ty, self.inst)
        self.p.inlined += 1
        self.scopes, self.ret, self.ret_ty, self.inst = [self.scopes[0], scope], rv, rt, self.p.inlined
        self.calls.append(name)
        fend = p.loc()
        last = self.stmt(self.funcs[name].body, body, None, None, fend)
        if target is None or rv is None:
            p.rule(last, fend)  # (reaching the closing brace and using the value is undefined behaviour: no rule)
        self.calls.pop()
        self.scopes, self.ret, self.ret_ty, self.inst = saved
        if target is None:
            return fend
        if rv is None:
            raise Refused(f"the value of {name}, which returns none")
        nxt = p.loc()
        g = []
        val = self.copy_ptr(rv, target_ty, g) if rt[0] == "p" else self.conv(V(rv, rt), target_ty, g)
        p.rule(fend, nxt, g, {target: val})
        return nxt

    def top(self, name):
        """A recursive function's own copy, entered by a call whose frames below are forgotten; a return ends the run."""
        if name in self.tops:
            return self.tops[name]
        p = self.p
        ps, rt = self.sig(name)
        entry = p.loc()
        scope, slots = {}, []
        for x, t in ps:
            u = p.var(x, t)
            self.types[u] = t
            scope[x] = u
            slots.append(u)
        self.tops[name] = (entry, slots, ps)
        rv = None if rt == VOID else p.var(f"ret_{name}", rt)
        if rv:
            self.types[rv] = rt
        saved = (self.scopes, self.ret, self.ret_ty, self.inst, self.calls, self.loops)
        self.p.inlined += 1
        self.scopes, self.ret, self.ret_ty, self.inst, self.calls, self.loops = [self.scopes[0], scope], rv, rt, self.p.inlined, [name], 0
        last = self.stmt(self.funcs[name].body, entry, None, None, "lend")
        p.rule(last, "lend")
        self.scopes, self.ret, self.ret_ty, self.inst, self.calls, self.loops = saved
        return self.tops[name]

    def boundary(self, call, cur, target, target_ty):
        p, name = self.p, call.name.name
        p.features.add(f"recursion ({self.mode})")
        ps, rt = self.sig(name)
        g = []
        vals = self.args(call, ps, g)
        entry, slots, _ = self.top(name)
        p.rule(cur, entry, g, dict(zip(slots, vals)))
        if self.mode != "terminates":
            return p.loc()  # nothing after a call that is entered and never returns
        # the call returns: its value any of its type, every global it may write any value of its type
        nxt = p.loc()
        g2, upd = list(g), {}
        for gl in sorted(self.info["writes"][name]):
            u = self.scopes[0].get(gl)
            if u is None:
                continue
            if self.types[u][0] == "i":
                upd[u] = p.nondet(self.types[u], g2)
            elif self.types[u][0] == "a":
                for s in self.arrays[u][2].values():
                    upd[s] = p.nondet(self.arrays[u][0], g2)
            else:
                raise Refused("pointers in a recursive program")
        if target is not None:
            if rt == VOID:
                raise Refused(f"the value of {name}, which returns none")
            if rt[0] != "i":
                raise Refused("pointers in a recursive program")
            upd[target] = self.conv(V(p.nondet(rt, g2), rt), target_ty, g2)
        p.rule(cur, nxt, g2, upd)
        return nxt

    # Calls inside an expression: each evaluated first, into a fresh variable, inner calls before outer ones. Their
    # order is C's to choose (unspecified): where it can matter (a call may write a global or end the run) and two are
    # siblings, refused.
    def hoist(self, e, cur, keep=False, extra=()):
        """`keep`: e is a call itself, inlined by the caller: only its arguments' calls are hoisted. `extra`: the names
        the rest of the full expression reads (an assignment's target, read by += or by its index)."""
        calls = []

        def walk(x, cond):
            if x is e and keep:
                for a in (x.args.exprs if x.args else []):
                    walk(a, cond)
                return
            if isinstance(x, c_ast.FuncCall) and isinstance(x.name, c_ast.ID) and x.name.name in self.funcs:
                if cond:
                    raise Refused("a call in a conditional part of an expression (after && or ||, or in a ternary's branch)")
                for a in (x.args.exprs if x.args else []):
                    walk(a, cond)
                calls.append(x)
                return
            if isinstance(x, c_ast.BinaryOp) and x.op in ("&&", "||"):
                walk(x.left, cond)
                walk(x.right, True)
                return
            if isinstance(x, c_ast.TernaryOp):
                walk(x.cond, cond)
                walk(x.iftrue, True)
                walk(x.iffalse, True)
                return
            for _, ch in x.children():
                walk(ch, cond)
        walk(e, False)
        if not calls:
            return cur, e
        # what each call may do that another part of the expression could see: write a global, write through a
        # pointer (to anything: a local whose address was passed), end the run
        eff = {id(c): self.info["writes"][c.name.name] | ({"*"} if self.info["ptrwrites"][c.name.name] else set()) |
               ({"end"} if self.info["ends"][c.name.name] else set()) for c in calls}
        if len(calls) > 1 and any(eff.values()):
            nested = all(self.inside(calls[i], calls[i + 1]) for i in range(len(calls) - 1))
            if not nested:
                raise Refused("calls in one expression whose order can matter (a call may write a global or through a pointer, or end the run)")
        for c in calls:
            if not eff[id(c)] - {"end"}:
                continue
            rest = self.reads(e, skip=c) | set(extra)  # what the rest of the expression reads, unsequenced with c
            if "*" in eff[id(c)] and rest:
                raise Refused("a call that writes through a pointer in an expression that reads a variable (their order is unspecified)")
            if rest & eff[id(c)]:
                raise Refused("a call in an expression that reads a global the call writes (their order is unspecified)")
        subst = {}
        for c in calls:  # post-order: arguments' calls first
            name = c.name.name
            _, rt = self.sig(name)
            if rt == VOID:
                raise Refused(f"the value of {name}, which returns none")
            self.ntemp += 1
            tn = f"__call{self.ntemp}"
            u = self.p.var(f"t_{name}", rt)
            self.types[u] = rt
            self.scopes[-1][tn] = u
            cur = self.inline(self.replace(c, subst, top=True), cur, u, rt)
            subst[id(c)] = c_ast.ID(tn)
        return cur, self.replace(e, subst, top=keep)

    def inside(self, a, b):
        """Call a is inside call b's arguments."""
        found = []

        class F(c_ast.NodeVisitor):
            def generic_visit(s, n):
                if n is a:
                    found.append(1)
                for _, ch in n.children():
                    s.visit(ch)
        F().visit(b)
        return bool(found)

    def reads(self, e, skip=None):
        """The names e reads (not the functions it calls), leaving out the call `skip` (its arguments included)."""
        out = set()

        class R(c_ast.NodeVisitor):
            def visit_ID(s, n):
                out.add(n.name)

            def visit_FuncCall(s, n):
                if n is skip:
                    return
                for a in (n.args.exprs if n.args else []):
                    s.visit(a)
        R().visit(e)
        return out

    def replace(self, e, subst, top=False):
        if not top and id(e) in subst:
            return subst[id(e)]
        if isinstance(e, c_ast.BinaryOp):
            return c_ast.BinaryOp(e.op, self.replace(e.left, subst), self.replace(e.right, subst))
        if isinstance(e, c_ast.UnaryOp):
            return c_ast.UnaryOp(e.op, self.replace(e.expr, subst))
        if isinstance(e, c_ast.Cast):
            return c_ast.Cast(e.to_type, self.replace(e.expr, subst))
        if isinstance(e, c_ast.TernaryOp):
            return c_ast.TernaryOp(self.replace(e.cond, subst), self.replace(e.iftrue, subst), self.replace(e.iffalse, subst))
        if isinstance(e, c_ast.FuncCall):
            return c_ast.FuncCall(e.name, c_ast.ExprList([self.replace(a, subst) for a in e.args.exprs]) if e.args else None)
        if isinstance(e, c_ast.ArrayRef):
            return c_ast.ArrayRef(e.name, self.replace(e.subscript, subst))
        return e

    def lookup(self, name):
        for s in reversed(self.scopes):
            if name in s:
                return s[name]
        raise Refused(f"an undeclared name {name}")

    # --- pointers ---------------------------------------------------------------------------------------------------
    def ptr_value(self, e, g):
        """A pointer expression's value: 0 (null) or an object's number; reading an indeterminate or dangling pointer is
        undefined behaviour."""
        p = self.p
        while isinstance(e, c_ast.Cast):
            t = type_of(e.to_type)
            if t[0] != "p":
                raise Refused("a pointer converted to an integer")
            e = e.expr
        if isinstance(e, c_ast.Constant) and const_expr(e) == 0:
            return "0"
        if isinstance(e, c_ast.ID) and e.name == "NULL":
            return "0"
        if isinstance(e, c_ast.UnaryOp) and e.op == "&":
            if not isinstance(e.expr, c_ast.ID):
                raise Refused("the address of anything but a variable")
            u = self.lookup(e.expr.name)
            if self.types[u][0] != "i":
                raise Refused("the address of anything but an integer variable")
            if u not in self.addressable:
                raise Refused("the address of a variable that may end before the run (only globals and main's outermost locals)")
            k = self.cell_of(u)
            return str(k)
        if isinstance(e, c_ast.ID):
            u = self.lookup(e.name)
            if self.types[u][0] != "p":
                raise Refused("an integer used as a pointer")
            self.valid_ptr(u, g)
            return u
        raise Refused("pointer arithmetic or a pointer expression beyond a variable, &x, null or a call")

    def valid_ptr(self, u, g):
        # a read of a pointer: null, or an object that is alive (indeterminate or freed: undefined behaviour)
        self.ub += 1
        alts = [["=", u, "0"]]
        for k, (_, _, alive) in enumerate(self.cells(), 1):
            alts.append(["=", u, str(k)] if alive is None else ["and", ["=", u, str(k)], [">=", alive, "1"]])
        g.append(["or", *alts] if len(alts) > 1 else alts[0])

    def cells(self):
        """Every object a pointer can name in the whole program (the first pass's list: a pointer read early in the
        text can name an object whose address is taken later), or, in the first pass, the ones so far."""
        return self.all_cells if self.all_cells is not None else self.p.cells

    def cell_of(self, u):
        for k, (s, _, _) in enumerate(self.p.cells, 1):
            if s == u:
                return k
        self.p.cells.append((u, self.types[u], None))
        return len(self.p.cells)

    def deref_cases(self, e, g):
        """*p: the objects p can point to, each with its guard (p names it and it is alive and large enough)."""
        if not isinstance(e, c_ast.ID):
            raise Refused("pointer arithmetic or a dereference of anything but a pointer variable")
        u = self.lookup(e.name)
        t = self.types[u]
        if t[0] != "p":
            raise Refused("a dereference of an integer")
        pt = t[1]
        if pt[0] != "i":
            raise Refused("a dereference of a void pointer")
        if self.deref_ty is None:
            self.deref_ty = pt
        if self.deref_ty != pt:
            raise Refused("pointers of two pointee types")
        out = []
        for k, (s, ct, alive) in enumerate(self.cells(), 1):
            if alive is None and ct != pt:
                raise Refused("pointers of two pointee types")
            out.append(([["=", u, str(k)]] + ([["=", alive, "1"]] if alive is not None else []), s))
        return out

    def alloc(self, call, cur, target):
        """p = malloc(n), calloc(m, n), alloca(n): a fresh cell (its contents any value; calloc's 0); malloc and calloc
        may return null. A cell smaller than the pointee is alive but can't be read or written (alive = 2)."""
        p, name = self.p, call.name.name
        if self.loops or self.info["goto"] or self.info["recursive"]:
            raise Refused("an allocation that may run more than once (in a loop, with goto or recursion)")
        if name in ("alloca", "__builtin_alloca") and self.calls:
            raise Refused("alloca outside main")
        args = call.args.exprs if call.args else []
        g = []
        if name == "calloc":
            if len(args) != 2:
                raise Refused("calloc's arguments")
            size = ["*", self.conv(self.term(args[0], g), LONG(False), g), self.conv(self.term(args[1], g), LONG(False), g)]
        else:
            if len(args) != 1:
                raise Refused(f"{name}'s arguments")
            size = self.conv(self.term(args[0], g), LONG(False), g)
        ct = self.deref_hint
        if ct is None:
            raise Refused("an allocation no pointer reads")
        s = p.var("cell", ct)
        self.types[s] = ct
        alive = p.var("alive", ity(True, 32, 3))
        self.types[alive] = INT
        p.cells.append((s, ct, alive))
        k = len(p.cells)
        p.features.add("pointers")
        nxt = p.loc()
        content = "0" if name == "calloc" else p.nondet(ct, g)
        big = str(sizeof(ct))
        p.rule(cur, nxt, g + [[">=", size, big]], {target: str(k), s: content, alive: "1"})
        p.rule(cur, nxt, g + [["<", size, big]], {target: str(k), s: content, alive: "2"})
        if name in ("malloc", "calloc"):
            p.rule(cur, nxt, g, {target: "0", alive: "0"})
        return nxt

    def copy_ptr(self, src, to, g):
        if to[0] != "p":
            raise Refused("a pointer converted to an integer")
        self.valid_ptr(src, g)
        return src

    # --- expressions ------------------------------------------------------------------------------------------------
    def term(self, e, guards):
        """An integer expression's value (V); nondet calls add fresh values and their range to `guards`, undefined
        behaviour the guards that rule it out."""
        p = self.p
        if isinstance(e, c_ast.Constant):
            v, t = constant(e)
            return V(num(v), t)
        if isinstance(e, c_ast.ID):
            if e.name in ("true", "false") and not any(e.name in s for s in self.scopes):
                return V("1" if e.name == "true" else "0", INT)
            if e.name in ENUMS and not any(e.name in s for s in self.scopes):
                return V(num(ENUMS[e.name]), INT)
            u = self.lookup(e.name)
            t = self.types[u]
            if t[0] != "i":
                raise Refused("an array or pointer used as a value" if t[0] == "a" else "a pointer used as an integer")
            return V(u, t)
        if isinstance(e, c_ast.Cast):
            to = type_of(e.to_type)
            if to[0] != "i":
                raise Refused("a cast to a pointer used as an integer" if to[0] == "p" else "a cast to void used as a value")
            return V(self.conv(self.term(e.expr, guards), to, guards), to)
        if isinstance(e, c_ast.UnaryOp):
            if e.op in ("-", "+", "~"):
                v = self.term(e.expr, guards)
                t = promote(v.ty)
                v = self.as_type(v, t, guards)
                if e.op == "+":
                    return v
                sx = ["-", v.sx] if e.op == "-" else ["-", ["-", v.sx], "1"]
                if not t[1]:
                    return V(sx, t, True)
                return self.signed_result(sx, t, guards) if e.op == "-" else V(sx, t)
            if e.op in ("p++", "p--", "++", "--"):
                raise Refused("side effects inside an expression")
            if e.op == "!":
                return self.bool_value(e, guards)
            if e.op == "*":
                self.ub += 1
                cases = self.deref_cases(e.expr, guards)
                d = p.new("d")
                alts = [conj(*c, ["=", d, s]) for c, s in cases]
                guards.append(["or", *alts] if len(alts) > 1 else alts[0] if alts else "false")
                return V(d, self.deref_ty)
            if e.op == "&":
                raise Refused("a pointer used as an integer")
            if e.op == "sizeof":
                c = const_expr(e)
                if c is None:
                    raise Refused("sizeof of an expression")
                return V(str(c), LONG(False))
            raise Refused(f"the operator {e.op}")
        if isinstance(e, c_ast.BinaryOp):
            if e.op in ("+", "-", "*"):
                a, b = self.term(e.left, guards), self.term(e.right, guards)
                t = usual(a.ty, b.ty)
                a, b = self.as_type(a, t, guards), self.as_type(b, t, guards)
                if e.op == "*":
                    x, y = a.sx, b.sx
                    if cval(x) is None and cval(y) is None:
                        p.features.add("nonlinear")
                sx = [e.op, a.sx, b.sx]
                if not t[1]:
                    return V(sx, t, True)
                return self.signed_result(sx, t, guards)
            if e.op in ("/", "%"):
                a, b = self.term(e.left, guards), self.term(e.right, guards)
                t = usual(a.ty, b.ty)
                a, b = self.norm(self.as_type(a, t, guards), guards), self.norm(self.as_type(b, t, guards), guards)
                return self.divide(e.op, a, b, t, guards)
            if e.op in ("&", "|", "^", "<<", ">>"):
                raise Refused("bitwise operators and shifts")
            if e.op in ("<", "<=", ">", ">=", "==", "!=", "&&", "||"):
                return self.bool_value(e, guards)
            raise Refused(f"the operator {e.op}")
        if isinstance(e, c_ast.FuncCall):
            name = e.name.name if isinstance(e.name, c_ast.ID) else None
            if name in self.funcs:
                raise Refused("a call inside an expression")
            t = nondet_type(name)
            if t is not None:
                return V(p.nondet(t, guards), t)
            if name in ALLOC or name in ("free", "memcpy", "memset", "strlen"):
                raise Refused("pointers and the heap (malloc) beyond p = malloc(...), alloca(...) and free(p)")
            if name in self.funcs:
                raise Refused("a call inside an expression")
            raise Refused("calls to functions with no body")
        if isinstance(e, c_ast.TernaryOp):
            gc = []
            c = self.cond(e.cond, gc)
            ga, gb = [], []
            a, b = self.term(e.iftrue, ga), self.term(e.iffalse, gb)
            t = usual(a.ty, b.ty)
            a, b = self.norm(self.as_type(a, t, ga), ga), self.norm(self.as_type(b, t, gb), gb)
            r = p.new("c")
            guards += gc
            guards.append(["or", conj(c, *ga, ["=", r, a.sx]), conj(neg(c), *gb, ["=", r, b.sx])])
            return V(r, t)
        if isinstance(e, c_ast.ArrayRef):
            cases = self.element_cases(e, guards)
            if any(x[1] is None for x in cases):  # (const_reads keeps every element a read can see: checked here)
                raise Refused("an array of more than 64 elements read at an element the translation didn't keep")
            d = p.new("d")
            alts = [conj(*c, ["=", d, s]) for c, s, _ in cases]
            self.ub += 1
            if len(alts) == 1 and not cases[0][0]:
                return V(cases[0][1], cases[0][2])
            guards.append(["or", *alts] if len(alts) > 1 else alts[0] if alts else "false")
            return V(d, self.arrays[self.array_of(e)][0])
        if isinstance(e, c_ast.Assignment):
            raise Refused("side effects inside an expression")
        raise Refused(f"the expression {type(e).__name__}")

    def divide(self, op, a, b, t, g):
        """C's / and % (truncation toward zero): a fresh quotient q, the remainder a − b·q between 0 and b, its sign a's;
        by zero, undefined behaviour."""
        p = self.p
        p.features.add("division")
        q = p.new("q")
        r, nr = ["-", a.sx, ["*", b.sx, q]], ["-", ["*", b.sx, q], a.sx]
        k = cval(b.sx)
        if not (k is not None and k > 0):
            self.ub += 1
        if k is not None and k > 0:
            g.append(["or", ["and", [">=", a.sx, "0"], ["<=", "0", r], ["<", r, b.sx]], ["and", ["<", a.sx, "0"], ["<=", "0", nr], ["<", nr, b.sx]]])
        else:
            if k is None:
                p.features.add("nonlinear")
            if k == 0:
                g.append("false")
            nb = ["-", b.sx]
            g.append(["or", ["and", [">", b.sx, "0"], [">=", a.sx, "0"], ["<=", "0", r], ["<", r, b.sx]],
                      ["and", [">", b.sx, "0"], ["<", a.sx, "0"], ["<=", "0", nr], ["<", nr, b.sx]],
                      ["and", ["<", b.sx, "0"], [">=", a.sx, "0"], ["<=", "0", r], ["<", r, nb]],
                      ["and", ["<", b.sx, "0"], ["<", a.sx, "0"], ["<=", "0", nr], ["<", nr, nb]]])
        if t[1] and not (k is not None and k > 0):
            self.signed_result(q, t, g)  # INT_MIN / -1
        return V(q if op == "/" else r, t)

    def bool_value(self, e, guards):
        """A condition used as a value: 1 where it holds, else 0."""
        gc = []
        c = simp(self.cond(e, gc))
        guards += gc
        if c in ("true", "false"):
            return V("1" if c == "true" else "0", INT)
        r = self.p.new("c")
        guards.append(["or", ["and", c, ["=", r, "1"]], ["and", neg(c), ["=", r, "0"]]])
        return V(r, INT)

    def array_of(self, e):
        if not isinstance(e.name, c_ast.ID):
            raise Refused("arrays of arrays")
        u = self.lookup(e.name.name)
        if u not in self.arrays:
            raise Refused("pointer arithmetic (p[i])" if self.types.get(u, ("",))[0] == "p" else "an index into a non-array")
        return u

    def element_cases(self, e, g):
        """a[i]: the elements it can be, each with its guard (i is its index); out of bounds, undefined behaviour."""
        u = self.array_of(e)
        el, n, slots, full = self.arrays[u]
        i = self.norm(self.term(e.subscript, g), g)
        c = cval(i.sx)
        if c is not None:
            if not 0 <= c < n:
                return []
            if c in slots:
                return [([], slots[c], el)]
            return [([], None, el)]  # an element no read sees
        return [([["=", i.sx, str(k)]], s, el) for k, s in sorted(slots.items())] + \
            ([] if full else [([["<=", "0", i.sx], ["<", i.sx, str(n)]] + [["or", ["<", i.sx, str(k)], [">", i.sx, str(k)]] for k in sorted(slots)], None, el)])

    # a condition
    def cond(self, e, guards):
        if isinstance(e, c_ast.BinaryOp) and e.op in ("<", "<=", ">", ">=", "==", "!="):
            if self.is_ptr(e.left) or self.is_ptr(e.right):
                if e.op not in ("==", "!="):
                    raise Refused("pointer comparisons other than == and !=")
                a, b = self.ptr_value(e.left, guards), self.ptr_value(e.right, guards)
            else:
                x, y = self.term(e.left, guards), self.term(e.right, guards)
                t = usual(x.ty, y.ty)
                a = self.norm(self.as_type(x, t, guards), guards).sx
                b = self.norm(self.as_type(y, t, guards), guards).sx
            return ["or", ["<", a, b], [">", a, b]] if e.op == "!=" else ["=" if e.op == "==" else e.op, a, b]
        if isinstance(e, c_ast.BinaryOp) and e.op in ("&&", "||"):
            # the right side is evaluated only where the left decides nothing: its undefined behaviour only there
            gl, gr = [], []
            a = self.cond(e.left, gl)
            before = self.ub
            b = self.cond(e.right, gr)
            guards += gl
            if gr and self.ub == before:
                guards += gr  # only definitions (fresh values in range, quotients): true wherever evaluated or not
            elif gr:
                guards.append(["or", neg(a) if e.op == "&&" else a, conj(*gr)])
            return ["and" if e.op == "&&" else "or", a, b]
        if isinstance(e, c_ast.UnaryOp) and e.op == "!":
            return neg(self.cond(e.expr, guards))
        if isinstance(e, c_ast.ID) and e.name in ("true", "false") and not any(e.name in s for s in self.scopes):
            return e.name
        if isinstance(e, c_ast.Constant):
            return "false" if self.term(e, guards).sx == "0" else "true"
        if self.is_ptr(e):
            t = self.ptr_value(e, guards)
            return ["or", ["<", t, "0"], [">", t, "0"]]
        t = self.norm(self.term(e, guards), guards).sx
        return ["or", ["<", t, "0"], [">", t, "0"]]

    def is_ptr(self, e):
        while isinstance(e, c_ast.Cast):
            if type_of(e.to_type)[0] == "p":
                return True
            e = e.expr
        if isinstance(e, c_ast.ID) and e.name == "NULL":
            return True
        if isinstance(e, c_ast.UnaryOp) and e.op == "&":
            return True
        if isinstance(e, c_ast.ID):
            for s in reversed(self.scopes):
                if e.name in s:
                    return self.types[s[e.name]][0] == "p"
        return False

    # --- statements -------------------------------------------------------------------------------------------------
    def store(self, cur, lv, value, g):
        """lv = value(old, guards): one rule per object lv can be (an array element, a pointer's target), each with its
        guard; none where lv is out of bounds or invalid (undefined behaviour)."""
        p = self.p
        nxt = p.loc()
        if isinstance(lv, c_ast.ID):
            u = self.lookup(lv.name)
            t = self.types[u]
            if t[0] != "i":
                raise Refused("an assignment to an array" if t[0] == "a" else "a pointer assigned an integer")
            gg = list(g)
            p.rule(cur, nxt, gg, {u: self.conv(value(V(u, t), gg), t, gg)})
            return nxt
        if isinstance(lv, c_ast.ArrayRef):
            cases = self.element_cases(lv, g)
            el = self.arrays[self.array_of(lv)][0]
        elif isinstance(lv, c_ast.UnaryOp) and lv.op == "*":
            cases = [(c, s, self.deref_ty) for c, s in self.deref_cases(lv.expr, g)]
            el = self.deref_ty
        else:
            raise Refused("an assignment to anything but a variable, an array element or *p")
        for c, s, t in cases:
            gg = list(g) + c
            if s is None:  # an element no read sees: its value is evaluated, nothing kept
                d = p.new("d")
                val = value(V(d, el), gg)
                self.conv(val, el, gg)
                p.rule(cur, nxt, gg + [["<=", num(rng(el)[0]), d], ["<=", d, num(rng(el)[1])]])
                continue
            p.rule(cur, nxt, gg, {s: self.conv(value(V(s, t), gg), t, gg)})
        return nxt

    def assign_ptr(self, cur, u, e, g):
        p = self.p
        if isinstance(e, c_ast.FuncCall) and isinstance(e.name, c_ast.ID) and e.name.name in ALLOC:
            if g:
                raise Refused("an allocation with side conditions")
            return self.alloc(e, cur, u)
        inner = e
        while isinstance(inner, c_ast.Cast):
            inner = inner.expr
        if isinstance(inner, c_ast.FuncCall) and isinstance(inner.name, c_ast.ID) and inner.name.name in ALLOC:
            return self.alloc(inner, cur, u)
        if self.callee(inner):
            return self.inline(inner, cur, u, self.types[u])
        v = self.ptr_value(e, g)
        nxt = p.loc()
        p.rule(cur, nxt, g, {u: v})
        return nxt

    def decl(self, s, cur):
        p = self.p
        static = bool(s.storage and "static" in s.storage)
        if static and not self.main_top():
            raise Refused("static locals")
        if static and self.info["goto"]:
            raise Refused("static locals with goto")
        if s.storage and "extern" in s.storage:
            raise Refused("extern variables")
        k = type_of(s.type)
        if k == VOID:
            raise Refused("a void variable")
        if k[0] == "a":
            t = s.type
            while isinstance(t, c_ast.TypeDecl):
                t = t.type
            if isinstance(t, c_ast.ArrayDecl) and any(any(n in sc for sc in self.scopes) for n in self.reads(t.dim)):
                raise Refused("an array whose size reads a variable")  # (a name shadowing an enum constant)
            return self.decl_array(s, k, cur, zero=static)
        u = p.var(s.name, k)
        self.types[u] = k
        if self.main_top() and s.name in self.addr_taken:
            self.addressable.add(u)
        self.scopes[-1][s.name] = u
        if k[0] == "p":
            p.features.add("pointers")
            if s.init is None:
                nxt = p.loc()
                p.rule(cur, nxt, [], {u: "0" if static else "-1"})
                return nxt
            return self.assign_ptr(cur, u, s.init, [])
        g = []
        if s.init is not None and self.callee(s.init):
            return self.inline(s.init, cur, u, k)  # T x = f(...): f's value straight into x
        if s.init is not None:
            cur, init = self.hoist(s.init, cur)
            val = self.conv(self.term(init, g), k, g)
        else:
            val = "0" if static else p.nondet(k, g)  # a static local starts at 0 (C11 6.7.9p10)
        nxt = p.loc()
        p.rule(cur, nxt, g, {u: val})
        return nxt

    def decl_array(self, s, k, cur, zero):
        """An array: an element per variable (past 64 elements, the ones read at a constant index)."""
        p = self.p
        el, n = k[1], k[2]
        p.features.add("arrays")
        full = n <= 64
        if not full and s.name in self.array_bad:
            raise Refused("an array of more than 64 elements read at an index that is not a constant")
        idx = self.array_reads.get(s.name, set())
        keep = range(n) if full else sorted(i for i in idx if 0 <= i < n)
        u = f"arr_{s.name}_{len(self.arrays)}"
        slots = {}
        for i in keep:
            sl = p.var(f"{s.name}_{i}", el)
            self.types[sl] = el
            slots[i] = sl
        self.arrays[u] = (el, n, slots, full)
        self.types[u] = k
        self.scopes[-1][s.name] = u
        g, upd = [], {}
        inits = []
        if s.init is not None:
            if not isinstance(s.init, c_ast.InitList):
                raise Refused("an array initializer that isn't a list")
            inits = s.init.exprs
            if len(inits) > n:
                raise Refused("an array initializer longer than the array")
        for i, sl in slots.items():
            if i < len(inits):
                upd[sl] = self.conv(self.term(inits[i], g), el, g)
            elif zero or s.init is not None:
                upd[sl] = "0"
            else:
                upd[sl] = p.nondet(el, g)
        nxt = p.loc()
        p.rule(cur, nxt, g, upd)
        return nxt

    def stmt(self, s, cur, brk, cont, end):
        p = self.p
        if s is None or isinstance(s, c_ast.EmptyStatement):
            return cur
        if isinstance(s, c_ast.Compound):
            self.scopes.append({})
            for x in s.block_items or []:
                cur = self.stmt(x, cur, brk, cont, end)
            self.scopes.pop()
            return cur
        if isinstance(s, c_ast.Decl):
            if isinstance(s.type, c_ast.FuncDecl):
                return cur
            return self.decl(s, cur)
        if isinstance(s, c_ast.DeclList):
            for d in s.decls:
                cur = self.stmt(d, cur, brk, cont, end)
            return cur
        if isinstance(s, c_ast.Assignment):
            if isinstance(s.lvalue, c_ast.ID) and self.types.get(self.lookup(s.lvalue.name), ("",))[0] == "p":
                if s.op != "=":
                    raise Refused("pointer arithmetic")
                return self.assign_ptr(cur, self.lookup(s.lvalue.name), s.rvalue, [])
            if s.op == "=" and isinstance(s.lvalue, c_ast.ID) and self.callee(s.rvalue):
                u = self.lookup(s.lvalue.name)
                return self.inline(s.rvalue, cur, u, self.types[u])
            # the target's own reads (its index, the pointer, or itself for +=) are unsequenced with the right side's calls
            cur, rv = self.hoist(s.rvalue, cur, extra=() if s.op == "=" and isinstance(s.lvalue, c_ast.ID) else self.reads(s.lvalue))
            g = []
            r = self.term(rv, g)
            if s.op == "=":
                return self.store(cur, s.lvalue, lambda old, gg: r, g)
            op = s.op[:-1]
            if op in ("+", "-", "*", "/", "%"):
                return self.store(cur, s.lvalue, lambda old, gg: self.binop(op, old, r, gg), g)
            raise Refused("bitwise operators and shifts")
        if isinstance(s, c_ast.UnaryOp) and s.op in ("p++", "p--", "++", "--"):
            if isinstance(s.expr, c_ast.ID) and self.types.get(self.lookup(s.expr.name), ("",))[0] == "p":
                raise Refused("pointer arithmetic")
            d = "+" if "++" in s.op else "-"
            return self.store(cur, s.expr, lambda old, gg: self.binop(d, old, V("1", INT), gg), [])
        if isinstance(s, c_ast.Cast) and type_of(s.to_type) == VOID:
            return self.stmt(s.expr, cur, brk, cont, end)
        if isinstance(s, c_ast.FuncCall):
            name = s.name.name if isinstance(s.name, c_ast.ID) else None
            if name in self.funcs:  # the task's own definition first (a reach_error that returns, say)
                return self.inline(s, cur)
            if name in ASSUME:
                cur, a = self.hoist(s.args.exprs[0], cur)
                g = []
                c = self.cond(a, g)
                nxt = p.loc()
                p.rule(cur, nxt, g + [c])
                return nxt
            if name in ENDS:
                p.rule(cur, self.pend)
                return p.loc()  # unreachable from here
            if name in self.funcs:
                return self.inline(s, cur)
            if name == "free":
                return self.free(s, cur)
            if nondet_type(name) is not None:
                g = []
                self.term(s, g)
                nxt = p.loc()
                p.rule(cur, nxt, g)
                return nxt
            if name in ALLOC:
                raise Refused("an allocation whose pointer is dropped")
            raise Refused("calls to functions with no body")
        if isinstance(s, c_ast.If):
            cur, ce = self.hoist(s.cond, cur)
            g = []
            c = self.cond(ce, g)
            t, f, j = p.loc(), p.loc(), p.loc()
            p.rule(cur, t, g + [c])
            p.rule(cur, f, g + [neg(c)])
            p.rule(self.stmt(s.iftrue, t, brk, cont, end), j)
            p.rule(self.stmt(s.iffalse, f, brk, cont, end), j)
            return j
        if isinstance(s, c_ast.While):
            head, body, out = p.loc(), p.loc(), p.loc()
            p.rule(cur, head)
            test, ce = self.hoist(s.cond, head)
            g = []
            c = self.cond(ce, g)
            p.rule(test, body, g + [c])
            p.rule(test, out, g + [neg(c)])
            self.loops += 1
            p.rule(self.stmt(s.stmt, body, out, head, end), head)
            self.loops -= 1
            return out
        if isinstance(s, c_ast.DoWhile):
            body, test, out = p.loc(), p.loc(), p.loc()
            p.rule(cur, body)
            self.loops += 1
            p.rule(self.stmt(s.stmt, body, out, test, end), test)
            self.loops -= 1
            t2, ce = self.hoist(s.cond, test)
            g = []
            c = self.cond(ce, g)
            p.rule(t2, body, g + [c])
            p.rule(t2, out, g + [neg(c)])
            return out
        if isinstance(s, c_ast.For):
            self.scopes.append({})
            cur = self.stmt(s.init, cur, brk, cont, end)
            head, body, step, out = p.loc(), p.loc(), p.loc(), p.loc()
            p.rule(cur, head)
            g = []
            test, ce = (head, None) if s.cond is None else self.hoist(s.cond, head)
            c = self.cond(ce, g) if ce is not None else "true"
            p.rule(test, body, g + [c])
            p.rule(test, out, g + [neg(c)])
            self.loops += 1
            p.rule(self.stmt(s.stmt, body, out, step, end), step)
            p.rule(self.stmt(s.next, step, out, step, end) if not isinstance(s.next, c_ast.ExprList) else self.exprs(s.next, step, end), head)
            self.loops -= 1
            self.scopes.pop()
            return out
        if isinstance(s, c_ast.ExprList):
            return self.exprs(s, cur, end)
        if isinstance(s, c_ast.Break):
            if brk is None:
                raise Refused("break outside a loop")
            p.rule(cur, brk)
            return p.loc()
        if isinstance(s, c_ast.Continue):
            p.rule(cur, cont)
            return p.loc()
        if isinstance(s, c_ast.Return):
            if s.expr is not None and self.ret is not None and self.calls:
                if self.ret_ty[0] == "p":
                    g = []
                    nxt = self.assign_ptr(cur, self.ret, s.expr, g)
                    p.rule(nxt, end)
                    return p.loc()
                if self.callee(s.expr):
                    cur = self.inline(s.expr, cur, self.ret, self.ret_ty)
                    p.rule(cur, end)
                    return p.loc()
                cur, ex = self.hoist(s.expr, cur)
                g = []
                v = self.conv(self.term(ex, g), self.ret_ty, g)
                p.rule(cur, end, g, {self.ret: v})
                return p.loc()
            if s.expr is not None:
                if self.callee(s.expr):
                    cur = self.inline(s.expr, cur)
                    p.rule(cur, end)
                    return p.loc()
                cur, ex = self.hoist(s.expr, cur)
                if not self.is_ptr(ex):
                    self.term(ex, [])  # (its undefined behaviour ends the run too)
                p.rule(cur, end)
                return p.loc()
            p.rule(cur, end)
            return p.loc()
        if isinstance(s, c_ast.Label):
            at = p.labels.setdefault((self.inst, s.name), p.loc())
            p.rule(cur, at)
            return self.stmt(s.stmt, at, brk, cont, end)
        if isinstance(s, c_ast.Goto):
            at = p.labels.setdefault((self.inst, s.name), p.loc())
            p.rule(cur, at)
            return p.loc()
        if isinstance(s, c_ast.Switch):
            raise Refused("switch")
        if isinstance(s, (c_ast.BinaryOp, c_ast.ID, c_ast.Constant, c_ast.UnaryOp, c_ast.Cast, c_ast.TernaryOp, c_ast.ArrayRef)):
            # an expression evaluated for nothing: its calls and undefined behaviour still happen
            cur, ex = self.hoist(s, cur)
            g = []
            self.term(ex, g)
            nxt = p.loc()
            p.rule(cur, nxt, g)
            return nxt
        raise Refused(f"the statement {type(s).__name__}")

    def binop(self, op, a, b, g):
        t = usual(a.ty, b.ty)
        a, b = self.as_type(a, t, g), self.as_type(b, t, g)
        if op in ("/", "%"):
            return self.divide(op, self.norm(a, g), self.norm(b, g), t, g)
        sx = [op, a.sx, b.sx]
        if op == "*" and cval(a.sx) is None and cval(b.sx) is None:
            self.p.features.add("nonlinear")
        if not t[1]:
            return V(sx, t, True)
        return self.signed_result(sx, t, g)

    def free(self, s, cur):
        """free(p): p null, nothing; p a live allocated cell, the cell dead (anything else: undefined behaviour)."""
        p = self.p
        args = s.args.exprs if s.args else []
        e = args[0] if len(args) == 1 else None
        while isinstance(e, c_ast.Cast):
            e = e.expr
        if not isinstance(e, c_ast.ID):
            raise Refused("free of anything but a pointer variable")
        u = self.lookup(e.name)
        nxt = p.loc()
        p.rule(cur, nxt, [["=", u, "0"]])
        for k, (_, _, alive) in enumerate(self.cells(), 1):
            if alive is not None:
                p.rule(cur, nxt, [["=", u, str(k)], [">=", alive, "1"]], {alive: "0"})
        return nxt

    def exprs(self, es, cur, end):
        for e in es.exprs:
            cur = self.stmt(e, cur, None, None, end)
        return cur


def prescan(nodes):
    """The most basic reason first: the data the program keeps (structs, floats), before what its code does."""
    seen = set()

    class Vis(c_ast.NodeVisitor):
        def visit_Struct(self, n):
            seen.add("structs")

        def visit_Union(self, n):
            seen.add("structs")

        def visit_IdentifierType(self, n):
            if "float" in n.names or "double" in n.names:
                seen.add("floats")

        def visit_Constant(self, n):
            if n.type in ("float", "double"):
                seen.add("floats")

        def visit_FuncCall(self, n):
            if isinstance(n.name, c_ast.ID) and n.name.name in ("__VERIFIER_nondet_float", "__VERIFIER_nondet_double"):
                seen.add("floats")
            self.generic_visit(n)
    for x in nodes:
        Vis().visit(x)
    for k, why in (("structs", "structs"), ("floats", "floats")):
        if k in seen:
            raise Refused(why)


HEADERS = ("stdlib.h", "stdio.h", "assert.h", "stdbool.h")


def clean(text):
    """What pycparser doesn't read, left out: lines spliced (backslash-newline) and comments, as C's translation phases
    2 and 3 do; then the preprocessor's directives: #include of a standard header whose names the translation knows
    (malloc, NULL, bool, true, false; any other name it declares is refused where it is used) and line markers, left
    out; any other directive (#define, #if, ...) refused. Then GCC's __attribute__((...)), __extension__, __restrict,
    __inline."""
    text = text.replace("\\\n", "")
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    text = re.sub(r"//[^\n]*", "", text)
    for l in re.findall(r"^\s*#[^\n]*", text, flags=re.M):
        d = l.strip()[1:].strip()
        m = re.fullmatch(r'include\s*[<"]([\w./]+)[>"]', d)
        if m and m.group(1) in HEADERS or re.fullmatch(r'(line\s+)?\d+(\s+"[^"]*")?(\s+\d+)*', d):
            continue
        raise Refused(f"a preprocessor directive (#{d.split()[0] if d.split() else ''})")
    text = re.sub(r"^\s*#[^\n]*", "", text, flags=re.M)
    out, i = [], 0
    while i < len(text):
        if text.startswith("__attribute__", i):
            j = text.index("(", i)
            depth = 0
            while True:
                depth += {"(": 1, ")": -1}.get(text[j], 0)
                j += 1
                if depth == 0:
                    break
            i = j
            continue
        out.append(text[i])
        i += 1
    s = "".join(out)
    for w in ("__extension__", "__restrict", "__inline__", "__inline", "__const"):
        s = s.replace(w, "")
    return s


def analyse(main, funcs, globs):
    """Per function, what the translation needs to know: the globals it may write (with its callees'), whether it may
    end the run, the recursive functions; the program's goto and its arrays' constant reads."""
    gnames = {d.name for d in globs}

    def direct(f):
        calls, writes, ends = set(), set(), False
        local = set()

        class Vis(c_ast.NodeVisitor):
            def visit_Decl(s, n):
                if n.name:
                    local.add(n.name)
                s.generic_visit(n)

            def visit_FuncCall(s, n):
                nonlocal ends
                if isinstance(n.name, c_ast.ID):
                    if n.name.name in funcs:
                        calls.add(n.name.name)
                    if (n.name.name in ENDS or n.name.name in ASSUME) and n.name.name not in funcs:
                        ends = True
                s.generic_visit(n)

            def visit_Assignment(s, n):
                if isinstance(n.lvalue, c_ast.ID):
                    writes.add(n.lvalue.name)
                elif isinstance(n.lvalue, c_ast.ArrayRef) and isinstance(n.lvalue.name, c_ast.ID):
                    writes.add(n.lvalue.name.name)
                elif isinstance(n.lvalue, c_ast.UnaryOp) and n.lvalue.op == "*":
                    writes.add("*")
                s.generic_visit(n)

            def visit_UnaryOp(s, n):
                if n.op in ("p++", "p--", "++", "--"):
                    x = n.expr
                    if isinstance(x, c_ast.ID):
                        writes.add(x.name)
                    elif isinstance(x, c_ast.ArrayRef) and isinstance(x.name, c_ast.ID):
                        writes.add(x.name.name)
                    else:
                        writes.add("*")
                s.generic_visit(n)
        Vis().visit(f)
        params = {x.name for x in (f.decl.type.args.params if f.decl.type.args else []) if not isinstance(x, c_ast.Typename)}
        # a write to a name the function declares is (conservatively) a global's only where a global has the name
        return calls, {w for w in writes if w == "*" or w in gnames}, ends, params | local

    d = {k: direct(f) for k, f in funcs.items()}
    graph = {k: v[0] for k, v in d.items()}
    graph["main"] = direct(main)[0]

    def reach(k):
        seen, todo = set(), [k]
        while todo:
            x = todo.pop()
            for y in graph.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        return seen
    rec = {k for k in funcs if k in reach(k) and k in reach("main")}
    writes = {k: set(d[k][1]).union(*[d[j][1] for j in reach(k)]) for k in funcs}
    ends = {k: d[k][2] or any(d[j][2] for j in reach(k)) for k in funcs}
    ptrwrites = {k: "*" in writes[k] for k in funcs}
    for k in funcs:
        if "*" in writes[k]:
            writes[k] = set(writes[k]) | gnames
            writes[k].discard("*")
    gotos, addr, ptrs = [False], set(), [False]

    class Vis(c_ast.NodeVisitor):
        def visit_Goto(s, n):
            gotos[0] = True

        def visit_PtrDecl(s, n):
            ptrs[0] = True
            s.generic_visit(n)

        def visit_UnaryOp(s, n):
            if n.op == "&" and isinstance(n.expr, c_ast.ID):
                addr.add(n.expr.name)
            if n.op == "*":
                ptrs[0] = True
            s.generic_visit(n)
    for f in [main, *funcs.values(), *globs]:
        Vis().visit(f)
    return {"writes": writes, "ptrwrites": ptrwrites, "ends": ends, "recursive": rec, "goto": gotos[0], "addr": addr, "pointers": ptrs[0]}


def const_index(e):
    """An index the translation reads as this same constant whatever the scope: decimal, octal or hex int constants
    under + - * and unary -, every value in int's range (no name, no suffix, no conversion), or None."""
    if isinstance(e, c_ast.Constant):
        if e.type != "int" or re.search(r"[uUlL]", e.value):
            return None
        try:
            v, t = constant(e)
        except Refused:
            return None
        return v if t == INT else None
    if isinstance(e, c_ast.UnaryOp) and e.op in ("-", "+"):
        v = const_index(e.expr)
        v = None if v is None else (-v if e.op == "-" else v)
    elif isinstance(e, c_ast.BinaryOp) and e.op in ("+", "-", "*"):
        a, b = const_index(e.left), const_index(e.right)
        if a is None or b is None:
            return None
        v = a + b if e.op == "+" else a - b if e.op == "-" else a * b
    else:
        return None
    return v if v is not None and rng(INT)[0] <= v <= rng(INT)[1] else None


def const_reads(funcs_and_main):
    """For each array name, the constant indices it is read at, or absent where some read's index is not constant
    (a write at a non-constant index is fine: `a[i] = e` changes nothing a constant read doesn't see)."""
    reads, bad = {}, set()

    def visit(n, lhs=False):
        if isinstance(n, c_ast.Assignment):
            if isinstance(n.lvalue, c_ast.ArrayRef) and n.op == "=":
                lv = n.lvalue
                c = const_index(lv.subscript)
                if isinstance(lv.name, c_ast.ID) and c is not None:
                    reads.setdefault(lv.name.name, set()).add(c)  # written at a constant: kept
                visit(lv.subscript)
                visit(n.rvalue)
                return
            visit(n.lvalue)
            visit(n.rvalue)
            return
        if isinstance(n, c_ast.ArrayRef) and isinstance(n.name, c_ast.ID):
            c = const_index(n.subscript)
            if c is None:
                bad.add(n.name.name)
            else:
                reads.setdefault(n.name.name, set()).add(c)
            visit(n.subscript)
            return
        for _, ch in n.children():
            visit(ch)
    for f in funcs_and_main:
        visit(f)
    return reads, bad


def translate(text, data_model="LP64", no_overflow=False, mode=None, depth=None):
    DM["long"] = 64 if data_model == "LP64" else 32
    DM["ptr"] = 64 if data_model == "LP64" else 32
    TYPEDEFS.clear()
    ENUMS.clear()
    ENUM_TAGS.clear()
    ast = c_parser.CParser().parse(clean(text))
    main = None
    globs, funcs = [], {}
    for ext in ast.ext:
        if isinstance(ext, c_ast.Typedef):
            try:
                TYPEDEFS[ext.name] = type_of(ext.type)
            except Refused as e:
                TYPEDEFS[ext.name] = e
        elif isinstance(ext, c_ast.FuncDef):
            if ext.decl.name == "main":
                main = ext
            else:
                funcs[ext.decl.name] = ext
        elif isinstance(ext, c_ast.Decl):
            if isinstance(ext.type, c_ast.FuncDecl):
                continue
            en = ext.type if isinstance(ext.type, c_ast.Enum) else ext.type.type if isinstance(ext.type, c_ast.TypeDecl) else None
            if isinstance(en, c_ast.Enum) and ext.name is None:
                enum_type(en)
                continue
            if ext.name is None:
                continue
            globs.append(ext)
    if main is None:
        raise Refused("no main")
    # every function the task defines is its own, but an end (reach_error, abort, ...) whose body is just a call to an
    # end the task doesn't define (`void reach_error() { __assert_fail(...); }`), which ends the run as that one does
    for k in [k for k, f in funcs.items() if k in ENDS]:
        items = funcs[k].body.block_items or []
        if len(items) == 1 and isinstance(items[0], c_ast.FuncCall) and isinstance(items[0].name, c_ast.ID) and \
                items[0].name.name in ENDS and items[0].name.name not in funcs:
            del funcs[k]
    prescan([main, *funcs.values(), *globs])
    info = analyse(main, funcs, globs)
    if info["recursive"] and mode not in ("terminates", "nonterminating"):
        raise Refused("recursion (translated with --for terminates or --for nonterminating)")
    if info["recursive"] and info["pointers"]:
        raise Refused("pointers in a recursive program")
    if info["goto"] and info["pointers"]:
        raise Refused("pointers with goto")
    if not info["recursive"]:
        return build(main, funcs, globs, info, no_overflow, None, 1)
    if mode == "terminates":
        return build(main, funcs, globs, info, no_overflow, mode, 0)
    # the deepest exact inlining that keeps the system small
    for L in ([depth] if depth else (4, 3, 2, 1)):
        prog, start = build(main, funcs, globs, info, no_overflow, mode, L)
        if L == 1 or len(prog.rules) * max(1, len(prog.vars)) <= 400_000:
            prog.features.add(f"recursion inlined {L} deep")
            return prog, start


def build(main, funcs, globs, info, no_overflow, mode, depth):
    """The system; where pointers name objects, twice: the second pass's dereferences know every object the first
    found (the same objects, numbered the same, the passes being the same code on the same program)."""
    prog, start = build1(main, funcs, globs, info, no_overflow, mode, depth, None)
    if not prog.cells:
        return prog, start
    prog2, start2 = build1(main, funcs, globs, info, no_overflow, mode, depth, list(prog.cells))
    assert prog2.cells == prog.cells
    return prog2, start2


def build1(main, funcs, globs, info, no_overflow, mode, depth, all_cells):
    prog = Program(no_overflow)
    m = Main(prog, funcs, info, mode, depth)
    m.all_cells = all_cells
    m.addr_taken = info["addr"]
    m.addressable = set()
    m.deref_ty = None
    m.array_reads, m.array_bad = const_reads([main, *funcs.values()])
    # the one pointee type every dereference reads (an allocation's cell holds it)
    hint = set()

    class P(c_ast.NodeVisitor):
        def visit_Decl(s, n):
            try:
                t = type_of(n.type)
                if t[0] == "p" and t[1][0] == "i":
                    hint.add(t[1])
            except Refused:
                pass
            s.generic_visit(n)
    for f in [main, *funcs.values(), *globs]:
        P().visit(f)
    m.deref_hint = hint.pop() if len(hint) == 1 else None
    if len(hint) > 0:
        raise Refused("pointers of two pointee types")
    start, first = prog.loc(), prog.loc()
    # globals: their initializers, or 0
    cur = first
    for d in globs:
        k = type_of(d.type)
        if k[0] == "a":
            cur = m.decl_array(d, k, cur, zero=True)
            continue
        u = prog.var(d.name, k)
        m.types[u] = k
        if d.name in m.addr_taken:
            m.addressable.add(u)
        m.scopes[0][d.name] = u
        g = []
        if k[0] == "p":
            val = m.ptr_value(d.init, g) if d.init is not None else "0"
        else:
            val = m.conv(m.term(d.init, g), k, g) if d.init is not None else "0"
        nxt = prog.loc()
        prog.rule(cur, nxt, g, {u: val})
        cur = nxt
    end = "lend"
    last = m.stmt(main.body, cur, None, None, end)
    prog.rule(last, end)
    # the entry's values are overwritten at once: each variable a fresh value of its type (globals then get theirs)
    # (each is written before it is read: a 64-bit type's range, past what the kernel's numbers hold, is left out)
    vs = prog.vars
    g0 = []
    # (with goto a declaration can be jumped past, and a variable read before it is written: the range kept)
    init = {v: prog.nondet(prog.kinds[v] if prog.kinds[v][0] != "i" or rng(prog.kinds[v])[1] < 2 ** 53 or info["goto"] else ("u",), g0) for v in vs}
    prog.rules.insert(0, (start, first, g0, init))
    return prog, start


def emit(prog, start):
    vs = prog.vars or ["dummy"]
    locs = sorted({r[0] for r in prog.rules} | {r[1] for r in prog.rules}, key=lambda l: (l != start, l))
    out = ["(format LCTRS)", "(theory Ints)"]
    sig = " ".join(["Int"] * len(vs))
    for l in locs:
        out.append(f"(fun {l} (-> {sig} Int))")
    out.append(f"(entrypoint {start})")

    def sx(s):
        return s if isinstance(s, str) else "(" + " ".join(sx(x) for x in s) + ")"
    for a, b, guards, upd in prog.rules:
        rhs = [upd.get(v, v) for v in vs]
        guards = [simp(x) for x in guards]
        guards = [["<", "1", "0"]] if "false" in guards else [x for x in guards if x != "true"]
        g = (["and", *guards] if len(guards) > 1 else guards[0]) if guards else None
        line = f"(rule ({a} {' '.join(vs)}) ({b} {' '.join(sx(x) for x in rhs)})"
        if g:
            line += f" :guard {sx(g)}"
        out.append(line + ")")
    return "\n".join(out) + "\n"


def read_yml(path):
    """The task's data model and whether it declares that no signed operation overflows (no-overflow.prp true)."""
    t = open(path).read()
    dm = re.search(r"data_model:\s*(\w+)", t)
    no = re.search(r"no-overflow\.prp\s*\n\s*expected_verdict:\s*(\w+)", t)
    return (dm.group(1) if dm else "LP64"), bool(no and no.group(1) == "true")


def main():
    args = sys.argv[1:]
    path = args[0]
    opt = lambda k: args[args.index(k) + 1] if k in args else None
    dm, no_overflow = read_yml(opt("--yml")) if opt("--yml") else ("LP64", False)
    dm = opt("--data-model") or dm
    unchecked = "--unchecked" in args and not no_overflow and "--no-overflow" not in args
    no_overflow = no_overflow or "--no-overflow" in args or unchecked
    mode = opt("--for")
    try:
        text = open(path).read()
        prog, start = translate(text, dm, no_overflow, mode)
        sys.stdout.write(emit(prog, start))
        split = any(f.startswith("recursion (") for f in prog.features)
        sys.stderr.write(json.dumps({"translated": True, "locations": prog.nlocs, "vars": len(prog.vars), "rules": len(prog.rules), "features": sorted(prog.features),
                                     "data_model": dm, "no_overflow": no_overflow, **({"for": mode} if split else {}), "split": split,
                                     **({"unchecked": True, "for": "terminates"} if unchecked else {})}) + "\n")
    except Refused as e:
        sys.stderr.write(json.dumps({"refused": str(e)}) + "\n")
        sys.exit(2)
    except RecursionError as e:
        sys.stderr.write(json.dumps({"refused": f"too deep: {e}"}) + "\n")
        sys.exit(2)
    except Exception as e:  # a parse error is a refusal too, with its message
        sys.stderr.write(json.dumps({"refused": f"parse: {type(e).__name__}: {str(e)[:160]}"}) + "\n")
        sys.exit(2)


if __name__ == "__main__":
    main()
