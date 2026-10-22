"""An SV-COMP termination task's C program as an ARI integer transition system: `python3 c2ari.py task.c > task.ari`.
Refused (exit 2, the reason on stderr as one JSON line) where the program leaves the subset below.

The subset: main and the functions it calls, each call inlined (f(...);, x = f(...); and return f(...);, its parameters
fresh variables set to the arguments, its body over the globals and them), over signed integer variables (int, long,
short, char, _Bool, enums; locals and globals); assignments, ++/--, compound assignments, if, while, do-while, for,
break, continue, return, goto and labels; expressions with + - * (products of variables too), / and % by a positive
constant k (the quotient a fresh value q with x − k·q in [0, k) for x >= 0 and k·q − x in [0, k) for x < 0: C's
truncation toward zero), comparisons, && || !, casts between those types; __VERIFIER_nondet_<signed type>() anywhere an
expression may be (a fresh value in the type's range), __VERIFIER_assume(c) (the run goes on only where c holds), and
abort(), exit(), reach_error(), __VERIFIER_error() (the run ends). The program's locations are the system's; a run is
the program's execution: every variable starts as C starts it (a global at its initializer or 0, a local at any value
of its type: reading it before it is written is undefined, so any value is what the task can do), and the entry's own
values are overwritten on the first step.

What the translation changes, said once here: arithmetic is on unbounded integers, the same as C's on every run where
no signed operation overflows (signed overflow is undefined behavior; the tasks' expected verdicts assume none), and a
long's (or long long's) values are left unbounded where C bounds them to 64 bits (counted in the output's features).

Refused, by reason, the data first (prescan): the heap (malloc), pointers, arrays, structs, floats, unsigned types
(arithmetic modulo 2^n); recursion (a cycle of calls from main); then the code: a call inside a larger expression,
calls to functions with no body; division or remainder by anything but a positive constant; bitwise operators and
shifts; the ternary operator, and a condition used as a value; side effects inside an expression (x++ in a
condition); switch.
"""
import json
import re
import sys

from pycparser import c_ast, c_parser

INT_RANGE = {"char": 8, "short": 16, "int": 32, "_Bool": 1}


class Refused(Exception):
    pass


def kind_of(t):
    """The integer kind of a declared type: ('int', bits) or ('long', None) for unbounded; refused otherwise."""
    while isinstance(t, c_ast.TypeDecl):
        t = t.type
    if isinstance(t, c_ast.PtrDecl):
        raise Refused("pointers")
    if isinstance(t, c_ast.ArrayDecl):
        raise Refused("arrays")
    if isinstance(t, c_ast.Struct) or isinstance(t, c_ast.Union):
        raise Refused("structs")
    if isinstance(t, c_ast.Enum):
        return ("int", 32)
    if isinstance(t, c_ast.IdentifierType):
        names = t.names
        if "unsigned" in names:
            raise Refused("unsigned types (arithmetic modulo 2^n)")
        if "float" in names or "double" in names:
            raise Refused("floats")
        if "long" in names:
            return ("long", None)
        for n in ("char", "short", "_Bool", "int"):
            if n in names:
                return ("int", INT_RANGE[n])
        if names == ["signed"]:
            return ("int", 32)
        if names[0] in TYPEDEFS:
            return TYPEDEFS[names[0]]
        if names == ["bool"]:
            return ("int", 1)
    raise Refused(f"the type {type(t).__name__} {getattr(t, 'names', '')}")


TYPEDEFS = {}


def range_of(kind):
    if kind[0] == "long":
        return None
    bits = kind[1]
    if bits == 1:
        return (0, 1)
    return (-(2 ** (bits - 1)), 2 ** (bits - 1) - 1)


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


def num(v):
    return str(v) if v >= 0 else ["-", str(-v)]


class Program:
    def __init__(self):
        self.vars = []  # unique names, in slot order
        self.kinds = {}
        self.rules = []  # (from, to, guards, updates{var: sx})
        self.nlocs = 0
        self.fresh = 0
        self.features = set()
        self.labels = {}
        self.inlined = 0

    def loc(self):
        self.nlocs += 1
        return f"l{self.nlocs - 1}"

    def var(self, name, kind):
        u = f"v_{name}" if f"v_{name}" not in self.kinds else f"v_{name}_{len(self.vars)}"
        self.vars.append(u)
        self.kinds[u] = kind
        if kind[0] == "long":
            self.features.add("long values unbounded")
        return u

    def nondet(self, kind, guards):
        self.fresh += 1
        v = f"nd_{self.fresh}"
        r = range_of(kind)
        if r:
            guards += [["<=", num(r[0]), v], ["<=", v, num(r[1])]]
        return v

    def rule(self, a, b, guards=(), updates=None):
        self.rules.append((a, b, list(guards), dict(updates or {})))


NONDET = {"__VERIFIER_nondet_int": ("int", 32), "__VERIFIER_nondet_long": ("long", None), "__VERIFIER_nondet_short": ("int", 16),
          "__VERIFIER_nondet_char": ("int", 8), "__VERIFIER_nondet_bool": ("int", 1), "__VERIFIER_nondet__Bool": ("int", 1)}
ENDS = {"abort", "exit", "reach_error", "__VERIFIER_error", "__assert_fail"}


class Main:
    def __init__(self, prog, funcs):
        self.p = prog
        self.scopes = [{}]
        self.funcs = funcs  # the program's other functions, inlined at each call
        self.calls = []  # the functions being inlined (a call to one of them is recursion)
        self.ret = None  # the variable a return writes, inside an inlined function
        self.pend = "lend"  # where abort(), exit() and the errors go
        self.inst = 0

    # f(args) at `cur`, inlined: its parameters fresh variables set to the arguments, its body over the globals and
    # them, each return to one location after it; `target`, the variable its value goes to.
    def inline(self, call, cur, end_unused, target=None):
        p, name = self.p, call.name.name
        if name in self.calls:
            raise Refused("recursion")
        f = self.funcs[name]
        params = [x for x in (f.decl.type.args.params if f.decl.type.args else []) if not (isinstance(x, c_ast.Typename))]
        args = call.args.exprs if call.args else []
        if len(params) != len(args):
            raise Refused(f"a call with {len(args)} arguments to {name} of {len(params)}")
        g = []
        vals = [self.term(a, g) for a in args]
        scope = {}
        upd = {}
        for x, v in zip(params, vals):
            u = p.var(x.name, kind_of(x.type))
            scope[x.name] = u
            upd[u] = v
        rt = f.decl.type.type
        void = isinstance(rt, c_ast.TypeDecl) and isinstance(rt.type, c_ast.IdentifierType) and rt.type.names == ["void"]
        rv = None if void else p.var(f"ret_{name}", kind_of(rt))
        body = p.loc()
        p.rule(cur, body, g, upd)
        saved = (self.scopes, self.ret, self.inst)
        self.p.inlined += 1
        self.scopes, self.ret, self.inst = [self.scopes[0], scope], rv, self.p.inlined
        self.calls.append(name)
        fend = p.loc()
        last = self.stmt(f.body, body, None, None, fend)
        p.rule(last, fend)
        self.calls.pop()
        self.scopes, self.ret, self.inst = saved
        if target is None:
            return fend
        if rv is None:
            raise Refused(f"the value of {name}, which returns none")
        nxt = p.loc()
        p.rule(fend, nxt, [], {target: rv})
        return nxt

    def why_call(self, name, inside):
        if name in ("malloc", "calloc", "realloc", "alloca", "__builtin_alloca", "free", "memcpy", "memset", "strlen"):
            return "pointers and the heap (malloc)"
        if name in self.funcs:
            return "a call inside an expression (only f(...);, x = f(...); and return f(...); are inlined)" if inside else "recursion"
        return "calls to functions with no body"

    def callee(self, e):
        return isinstance(e, c_ast.FuncCall) and isinstance(e.name, c_ast.ID) and e.name.name in self.funcs

    def lookup(self, name):
        for s in reversed(self.scopes):
            if name in s:
                return s[name]
        raise Refused(f"an undeclared name {name}")

    # an integer term; nondet calls add fresh values and their range to `guards`
    def term(self, e, guards):
        p = self.p
        if isinstance(e, c_ast.Constant):
            if e.type in ("int", "long int", "long long int") or e.type.startswith("int") or e.type.startswith("long"):
                v = e.value.rstrip("lLuU")
                if any(c in e.value.lower() for c in "u"):
                    raise Refused("unsigned types (arithmetic modulo 2^n)")
                return num(int(v, 0) if not (v.startswith("0") and len(v) > 1 and v[1].isdigit()) else int(v, 8))
            if e.type == "char":
                return num(ord(e.value.strip("'")))
            raise Refused(f"a constant of type {e.type}")
        if isinstance(e, c_ast.ID):
            if e.name in ("true", "false") and not any(e.name in s for s in self.scopes):
                return "1" if e.name == "true" else "0"
            if e.name in ENUMS:
                return num(ENUMS[e.name])
            return self.lookup(e.name)
        if isinstance(e, c_ast.Cast):
            kind_of(e.to_type.type)
            return self.term(e.expr, guards)
        if isinstance(e, c_ast.UnaryOp):
            if e.op == "-":
                return ["-", self.term(e.expr, guards)]
            if e.op == "+":
                return self.term(e.expr, guards)
            if e.op in ("p++", "p--", "++", "--"):
                raise Refused("side effects inside an expression")
            if e.op in ("!",):
                raise Refused("a condition used as a value")
            if e.op == "~":
                raise Refused("bitwise operators and shifts")
            if e.op in ("&", "*"):
                raise Refused("pointers")
            if e.op == "sizeof":
                raise Refused("sizeof")
            raise Refused(f"the operator {e.op}")
        if isinstance(e, c_ast.BinaryOp):
            if e.op in ("+", "-", "*"):
                if e.op == "*":
                    a, b = self.term(e.left, guards), self.term(e.right, guards)
                    if not isinstance(a, str) or not a.isdigit():
                        if not isinstance(b, str) or not b.isdigit():
                            if not (isinstance(a, list) and a[0] == "-" and isinstance(a[1], str) and a[1].isdigit()):
                                p.features.add("nonlinear")
                    return ["*", a, b]
                return [e.op, self.term(e.left, guards), self.term(e.right, guards)]
            if e.op in ("/", "%"):
                # by a positive constant k: q, C's quotient (toward zero), a fresh value with x − k·q in [0, k) where
                # x >= 0 and k·q − x in [0, k) where x < 0; the remainder x − k·q
                a, b = self.term(e.left, guards), self.term(e.right, guards)
                if not (isinstance(b, str) and b.isdigit() and int(b) > 0):
                    raise Refused("division or remainder by a term that is not a positive constant")
                p.features.add("division")
                p.fresh += 1
                q = f"q_{p.fresh}"
                r, nr = ["-", a, ["*", b, q]], ["-", ["*", b, q], a]
                guards.append(["or", ["and", [">=", a, "0"], ["<=", "0", r], ["<", r, b]], ["and", ["<", a, "0"], ["<=", "0", nr], ["<", nr, b]]])
                return q if e.op == "/" else r
            if e.op in ("&", "|", "^", "<<", ">>"):
                raise Refused("bitwise operators and shifts")
            raise Refused("a condition used as a value")
        if isinstance(e, c_ast.FuncCall):
            name = e.name.name if isinstance(e.name, c_ast.ID) else None
            if name in NONDET:
                return p.nondet(NONDET[name], guards)
            if name and name.startswith("__VERIFIER_nondet_u"):
                raise Refused("unsigned types (arithmetic modulo 2^n)")
            raise Refused(self.why_call(name, True))
        if isinstance(e, c_ast.TernaryOp):
            raise Refused("the ternary operator")
        if isinstance(e, c_ast.Assignment):
            raise Refused("side effects inside an expression")
        raise Refused(f"the expression {type(e).__name__}")

    # a condition
    def cond(self, e, guards):
        if isinstance(e, c_ast.BinaryOp) and e.op in ("<", "<=", ">", ">=", "==", "!="):
            a, b = self.term(e.left, guards), self.term(e.right, guards)
            return ["or", ["<", a, b], [">", a, b]] if e.op == "!=" else ["=" if e.op == "==" else e.op, a, b]
        if isinstance(e, c_ast.BinaryOp) and e.op in ("&&", "||"):
            return ["and" if e.op == "&&" else "or", self.cond(e.left, guards), self.cond(e.right, guards)]
        if isinstance(e, c_ast.UnaryOp) and e.op == "!":
            return neg(self.cond(e.expr, guards))
        if isinstance(e, c_ast.ID) and e.name in ("true", "false") and not any(e.name in s for s in self.scopes):
            return e.name
        if isinstance(e, c_ast.Constant):
            return "false" if self.term(e, guards) == "0" else "true"
        t = self.term(e, guards)
        return ["or", ["<", t, "0"], [">", t, "0"]]

    def assign(self, cur, name, sx_of, guards=None):
        guards = guards if guards is not None else []
        v = self.lookup(name)
        nxt = self.p.loc()
        self.p.rule(cur, nxt, guards, {v: sx_of(v)})
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
            k = kind_of(s.type)
            u = p.var(s.name, k)
            self.scopes[-1][s.name] = u
            g = []
            if s.init is not None and self.callee(s.init):
                return self.inline(s.init, cur, end, u)
            if s.init is not None:
                val = self.term(s.init, g)
            else:
                val = p.nondet(k, g)
            nxt = p.loc()
            p.rule(cur, nxt, g, {u: val})
            return nxt
        if isinstance(s, c_ast.DeclList):
            for d in s.decls:
                cur = self.stmt(d, cur, brk, cont, end)
            return cur
        if isinstance(s, c_ast.Assignment):
            if not isinstance(s.lvalue, c_ast.ID):
                raise Refused("pointers") if isinstance(s.lvalue, c_ast.UnaryOp) else Refused("arrays")
            g = []
            if s.op == "=" and self.callee(s.rvalue):
                return self.inline(s.rvalue, cur, end, self.lookup(s.lvalue.name))
            r = self.term(s.rvalue, g)
            if s.op == "=":
                return self.assign(cur, s.lvalue.name, lambda v: r, g)
            op = s.op[:-1]
            if op in ("+", "-", "*"):
                if op == "*":
                    p.features.add("nonlinear")
                return self.assign(cur, s.lvalue.name, lambda v: [op, v, r], g)
            if op in ("/", "%"):
                g2 = list(g)
                t = self.term(c_ast.BinaryOp(op, s.lvalue, s.rvalue), g2)
                return self.assign(cur, s.lvalue.name, lambda v: t, g2)
            raise Refused("bitwise operators and shifts")
        if isinstance(s, c_ast.UnaryOp) and s.op in ("p++", "p--", "++", "--"):
            if not isinstance(s.expr, c_ast.ID):
                raise Refused("pointers")
            d = "+" if "++" in s.op else "-"
            return self.assign(cur, s.expr.name, lambda v: [d, v, "1"])
        if isinstance(s, c_ast.FuncCall):
            name = s.name.name if isinstance(s.name, c_ast.ID) else None
            if name == "__VERIFIER_assume" or name == "assume_abort_if_not":
                g = []
                c = self.cond(s.args.exprs[0], g)
                nxt = p.loc()
                p.rule(cur, nxt, g + [c])
                return nxt
            if name in ENDS:
                p.rule(cur, self.pend)
                return p.loc()  # unreachable from here
            if name in self.funcs:
                return self.inline(s, cur, end)
            if name in NONDET:
                g = []
                self.term(s, g)
                nxt = p.loc()
                p.rule(cur, nxt, g)
                return nxt
            raise Refused(self.why_call(name, False))
        if isinstance(s, c_ast.If):
            g = []
            c = self.cond(s.cond, g)
            t, f, j = p.loc(), p.loc(), p.loc()
            p.rule(cur, t, g + [c])
            p.rule(cur, f, g + [neg(c)])
            p.rule(self.stmt(s.iftrue, t, brk, cont, end), j)
            p.rule(self.stmt(s.iffalse, f, brk, cont, end), j)
            return j
        if isinstance(s, c_ast.While):
            head, body, out = p.loc(), p.loc(), p.loc()
            p.rule(cur, head)
            g = []
            c = self.cond(s.cond, g)
            p.rule(head, body, g + [c])
            p.rule(head, out, g + [neg(c)])
            p.rule(self.stmt(s.stmt, body, out, head, end), head)
            return out
        if isinstance(s, c_ast.DoWhile):
            body, test, out = p.loc(), p.loc(), p.loc()
            p.rule(cur, body)
            p.rule(self.stmt(s.stmt, body, out, test, end), test)
            g = []
            c = self.cond(s.cond, g)
            p.rule(test, body, g + [c])
            p.rule(test, out, g + [neg(c)])
            return out
        if isinstance(s, c_ast.For):
            self.scopes.append({})
            cur = self.stmt(s.init, cur, brk, cont, end)
            head, body, step, out = p.loc(), p.loc(), p.loc(), p.loc()
            p.rule(cur, head)
            g = []
            c = self.cond(s.cond, g) if s.cond is not None else "true"
            p.rule(head, body, g + [c])
            p.rule(head, out, g + [neg(c)])
            p.rule(self.stmt(s.stmt, body, out, step, end), step)
            p.rule(self.stmt(s.next, step, out, step, end) if not isinstance(s.next, c_ast.ExprList) else self.exprs(s.next, step, end), head)
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
                if self.callee(s.expr):
                    cur = self.inline(s.expr, cur, end, self.ret)
                    p.rule(cur, end)
                    return p.loc()
                g = []
                v = self.term(s.expr, g)
                p.rule(cur, end, g, {self.ret: v})
                return p.loc()
            if s.expr is not None:
                self.term(s.expr, [])
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
        raise Refused(f"the statement {type(s).__name__}")

    def exprs(self, es, cur, end):
        for e in es.exprs:
            cur = self.stmt(e, cur, None, None, end)
        return cur


ENUMS = {}


def prescan(nodes):
    """The most basic reason first: the data the program keeps (heap, pointers, arrays, structs, floats, unsigned
    values), before what its code does."""
    seen = set()

    class V(c_ast.NodeVisitor):
        def visit_PtrDecl(self, n):
            seen.add("pointers")

        def visit_ArrayDecl(self, n):
            seen.add("arrays")

        def visit_ArrayRef(self, n):
            seen.add("arrays")

        def visit_Struct(self, n):
            seen.add("structs")

        def visit_FuncCall(self, n):
            if isinstance(n.name, c_ast.ID) and n.name.name in ("malloc", "calloc", "realloc", "alloca", "__builtin_alloca", "free"):
                seen.add("heap")
            self.generic_visit(n)

        def visit_IdentifierType(self, n):
            if "unsigned" in n.names:
                seen.add("unsigned")
            if "float" in n.names or "double" in n.names:
                seen.add("floats")
            if n.names and n.names[0] in UNSIGNED_TYPEDEFS:
                seen.add("unsigned")
    for x in nodes:
        V().visit(x)
    for k, why in (("heap", "pointers and the heap (malloc)"), ("pointers", "pointers"), ("arrays", "arrays"), ("structs", "structs"), ("floats", "floats"), ("unsigned", "unsigned types (arithmetic modulo 2^n)")):
        if k in seen:
            raise Refused(why)


UNSIGNED_TYPEDEFS = set()


def enum_value(v, i):
    if v is None:
        return i
    if isinstance(v, c_ast.UnaryOp) and v.op == "-":
        return -enum_value(v.expr, i)
    if isinstance(v, c_ast.Constant):
        return int(v.value.rstrip("lLuU"), 0)
    if isinstance(v, c_ast.ID) and v.name in ENUMS:
        return ENUMS[v.name]
    raise Refused("an enum value that isn't a constant")


def clean(text):
    """What pycparser doesn't read, left out: comments, preprocessor lines, and GCC's __attribute__((...)), __extension__,
    __restrict, __inline."""
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    text = re.sub(r"//[^\n]*", "", text)
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


def translate(text):
    ast = c_parser.CParser().parse(clean(text))
    prog = Program()
    main = None
    globs, funcs = [], {}
    for ext in ast.ext:
        if isinstance(ext, c_ast.Typedef):
            t = ext.type.type
            if isinstance(t, c_ast.Enum):
                for i, e in enumerate(t.values.enumerators if t.values else []):
                    ENUMS[e.name] = enum_value(e.value, i)
                TYPEDEFS[ext.name] = ("int", 32)
            else:
                try:
                    TYPEDEFS[ext.name] = kind_of(ext.type)
                except Refused as e:
                    if "unsigned" in str(e):
                        UNSIGNED_TYPEDEFS.add(ext.name)
        elif isinstance(ext, c_ast.FuncDef):
            if ext.decl.name == "main":
                main = ext
            elif ext.decl.name not in ENDS and ext.decl.name not in NONDET and ext.decl.name not in ("__VERIFIER_assume", "assume_abort_if_not"):
                funcs[ext.decl.name] = ext
        elif isinstance(ext, c_ast.Decl):
            if isinstance(ext.type, c_ast.FuncDecl):
                continue
            if isinstance(ext.type, c_ast.TypeDecl) and isinstance(ext.type.type, c_ast.Enum) and ext.name is None:
                for i, e in enumerate(ext.type.type.values.enumerators):
                    ENUMS[e.name] = enum_value(e.value, i)
                continue
            if ext.name is None:
                continue
            globs.append(ext)
    if main is None:
        raise Refused("no main")
    prescan([main, *funcs.values(), *globs])
    # recursion: a cycle of calls among the functions main reaches
    def calls(f):
        out = set()

        class V(c_ast.NodeVisitor):
            def visit_FuncCall(self, n):
                if isinstance(n.name, c_ast.ID) and n.name.name in funcs:
                    out.add(n.name.name)
                self.generic_visit(n)
        V().visit(f)
        return out
    graph = {k: calls(f) for k, f in funcs.items()}
    graph["main"] = calls(main)

    def cyclic(k, path):
        if k in path:
            return True
        return any(cyclic(j, path | {k}) for j in graph.get(k, ()))
    if cyclic("main", frozenset()):
        raise Refused("recursion")
    m = Main(prog, funcs)
    start, first = prog.loc(), prog.loc()
    # globals: their initializers, or 0
    cur = first
    for d in globs:
        k = kind_of(d.type)
        u = prog.var(d.name, k)
        m.scopes[0][d.name] = u
        g = []
        val = m.term(d.init, g) if d.init is not None else "0"
        nxt = prog.loc()
        prog.rule(cur, nxt, g, {u: val})
        cur = nxt
    end = "lend"
    last = m.stmt(main.body, cur, None, None, end)
    prog.rule(last, end)
    # labels a goto names but no statement defines
    # the entry's values are overwritten at once: each variable a fresh value of its type (globals then get theirs)
    vs = prog.vars
    g0 = []
    init = {v: prog.nondet(prog.kinds[v], g0) for v in vs}
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
        g = (["and", *guards] if len(guards) > 1 else guards[0]) if guards else None
        line = f"(rule ({a} {' '.join(vs)}) ({b} {' '.join(sx(x) for x in rhs)})"
        if g:
            line += f" :guard {sx(g)}"
        out.append(line + ")")
    return "\n".join(out) + "\n"


def main():
    path = sys.argv[1]
    try:
        text = open(path).read()
        prog, start = translate(text)
        sys.stdout.write(emit(prog, start))
        sys.stderr.write(json.dumps({"translated": True, "locations": prog.nlocs, "vars": len(prog.vars), "rules": len(prog.rules), "features": sorted(prog.features)}) + "\n")
    except Refused as e:
        sys.stderr.write(json.dumps({"refused": str(e)}) + "\n")
        sys.exit(2)
    except Exception as e:  # a parse error is a refusal too, with its message
        sys.stderr.write(json.dumps({"refused": f"parse: {type(e).__name__}: {str(e)[:160]}"}) + "\n")
        sys.exit(2)


if __name__ == "__main__":
    main()
