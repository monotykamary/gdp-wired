"""The gap between gdp-wired and Spacer on CHC-COMP's LIA-Lin track, by the shape of what Spacer found:
`python3 compare/chc/prof/gap.py --gdp <run dir> --others <run dir> --models <spacer models dir> --template <run dir>
[--cex <golem witnesses dir>] [--given <run dir>] [--write-given-models compare/chc/prof/given-models.json] --out <file.json>`.
--write-given-models writes Spacer's models of the sat gap's tasks (and the task names beside, -tasks.json) for
`modal_chc.py --tools given --tasks-json <that>`.

For each task Spacer answers sat and gdp-wired doesn't solve: Spacer's invariant (each predicate's interpretation, its
lets expanded, in CNF over linear atoms Σ c·x ≤ d, a yes/no literal or a literal no linear reading covers) and each
clause's shape against what inferLaws (core/infer.ts) builds, with the task's own coefficient magnitudes and shape
limits (prof/template.ts):
  - a unit clause: a bound of one value; two values with coefficients in the magnitudes (or ±1, past the limit); three
    values (unguarded, so at one predicate of several only through a counterexample's forms, ±1)
  - a yes/no literal or a choice's value beside a form of at most two values (a guard)
  - two linear literals: a counterexample's form, under a condition of one value or a sum or difference of two
  - anything else is outside: more than three values in one atom, three or more literals in a clause, a remainder or a
    quotient, a product, a quantifier
For each task some other tool answers unsat and gdp-wired doesn't: the length of Golem's derivation of false, beside
how far gdp-wired's runs went. Prints the counts and writes every task's classes to --out."""
import argparse
import collections
import json
import math
import re
import sys

sys.setrecursionlimit(100000)


def tokens(text):
    return re.findall(r"\(|\)|\|[^|]*\||[^\s()]+", text)


def parse(text):
    out, stack = [], [[]]
    for t in tokens(text):
        if t == "(":
            stack.append([])
        elif t == ")":
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t.strip("|"))
    return stack[0]


class Odd(Exception):
    """A term no linear reading covers: a product, a remainder, an ite over integers."""


def linear(e, env, flags):
    """e as {var: coef} and a constant."""
    if isinstance(e, str):
        if re.fullmatch(r"-?\d+", e):
            return {}, int(e)
        if e in env:
            return linear(env[e], env, flags)
        return {e: 1}, 0
    op, *xs = e
    if op == "+":
        acc, k = {}, 0
        for x in xs:
            m, c = linear(x, env, flags)
            k += c
            for v, a in m.items():
                acc[v] = acc.get(v, 0) + a
        return acc, k
    if op == "-":
        if len(xs) == 1:
            m, c = linear(xs[0], env, flags)
            return {v: -a for v, a in m.items()}, -c
        m, c = linear(xs[0], env, flags)
        m = dict(m)
        for x in xs[1:]:
            n, d = linear(x, env, flags)
            c -= d
            for v, a in n.items():
                m[v] = m.get(v, 0) - a
        return m, c
    if op == "*":
        parts = [linear(x, env, flags) for x in xs]
        k, var = 1, None
        for m, c in parts:
            if m:
                if var is not None:
                    flags.add("nonlinear")
                    raise Odd("product")
                var = (m, c)
            else:
                k *= c
        if var is None:
            return {}, k
        m, c = var
        return {v: a * k for v, a in m.items()}, c * k
    if op in ("mod", "div"):
        flags.add("modular")
        raise Odd(op)
    if op == "ite":
        flags.add("ite-term")
        raise Odd("ite")
    if op == "!":
        return linear(xs[0], env, flags)
    flags.add(f"op {op}")
    raise Odd(op)


BOOLOPS = {"and", "or", "not", "=>", "<=", ">=", "<", ">", "distinct", "xor", "true", "false"}


def is_bool(e, sorts, env):
    if isinstance(e, str):
        if e in ("true", "false"):
            return True
        if e in env:
            return is_bool(env[e], sorts, env)
        return sorts.get(e) == "Bool"
    op = e[0]
    if op in BOOLOPS or op == "exists" or op == "forall":
        return True
    if op == "=":
        return is_bool(e[1], sorts, env)
    if op == "ite":
        return is_bool(e[2], sorts, env)
    if op == "!":
        return is_bool(e[1], sorts, env)
    if op == "let":
        return is_bool(e[2], sorts, env)
    return False


# A formula in NNF: ("and", [..]) / ("or", [..]) / ("lit", atom). An atom: ("b", name, polarity) or
# ("le", frozenset(coef items), d) for Σ c·x ≤ d, or ("odd", text).
TRUE, FALSE = ("and", []), ("or", [])


def le_atom(m, c_left, rhs_m, c_right, strict):
    """left ≤ right (or <): Σ (l − r) ≤ c_right − c_left (− 1 if strict)."""
    coef = dict(m)
    for v, a in rhs_m.items():
        coef[v] = coef.get(v, 0) - a
    coef = {v: a for v, a in coef.items() if a != 0}
    d = c_right - c_left - (1 if strict else 0)
    if not coef:
        return TRUE if 0 <= d else FALSE
    return ("lit", ("le", frozenset(coef.items()), d))


def neg_le(atom):
    _, coef, d = atom
    return ("le", frozenset((v, -a) for v, a in coef), -d - 1)


def nnf(e, pos, sorts, env, flags, bound):
    if isinstance(e, str):
        if e == "true":
            return TRUE if pos else FALSE
        if e == "false":
            return FALSE if pos else TRUE
        if e in env:
            return nnf(env[e], pos, sorts, env, flags, bound)
        if e in bound:
            flags.add("quantified")
            return ("lit", ("odd", "quantified"))
        return ("lit", ("b", e, pos))
    op, *xs = e
    if op == "!":
        return nnf(xs[0], pos, sorts, env, flags, bound)
    if op == "let":
        inner = dict(env)
        for b in xs[0]:
            inner[b[0]] = b[1] if not isinstance(b[1], str) or b[1] not in env else env[b[1]]
        return nnf(xs[1], pos, sorts, inner, flags, bound)
    if op in ("exists", "forall"):
        flags.add("quantified")
        s = dict(sorts)
        for b in xs[0]:
            s[b[0]] = b[1]
        return nnf(xs[1], pos, s, env, flags, bound | {b[0] for b in xs[0]})
    if op == "not":
        return nnf(xs[0], not pos, sorts, env, flags, bound)
    if op == "and":
        return ("and" if pos else "or", [nnf(x, pos, sorts, env, flags, bound) for x in xs])
    if op == "or":
        return ("or" if pos else "and", [nnf(x, pos, sorts, env, flags, bound) for x in xs])
    if op == "=>":
        return nnf(["or", ["not", xs[0]], xs[1]], pos, sorts, env, flags, bound)
    if op == "xor":
        return nnf(["not", ["=", xs[0], xs[1]]], pos, sorts, env, flags, bound)
    if op == "ite" and is_bool(xs[1], sorts, env):
        c, a, b = xs
        return nnf(["and", ["or", ["not", c], a], ["or", c, b]], pos, sorts, env, flags, bound)
    if op == "=" and is_bool(xs[0], sorts, env):
        if len(xs) != 2:
            return nnf(["and", *[["=", xs[0], x] for x in xs[1:]]], pos, sorts, env, flags, bound)
        a, b = xs
        flags.add("iff")
        return nnf(["and", ["or", ["not", a], b], ["or", a, ["not", b]]], pos, sorts, env, flags, bound)
    if op in ("<=", ">=", "<", ">", "=", "distinct"):
        try:
            terms = [linear(x, env, flags) for x in xs]
        except Odd as why:
            return ("lit", ("odd", str(why)))
        if any(v in bound for m, _ in terms for v in m):
            flags.add("quantified")
            return ("lit", ("odd", "quantified"))
        pairs = list(zip(terms, terms[1:]))
        if op == "distinct":
            if len(terms) != 2:
                flags.add("distinct>2")
            return nnf(["not", ["=", *xs]], pos, sorts, env, flags, bound)
        parts = []
        for (lm, lc), (rm, rc) in pairs:
            if op == "<=":
                parts.append(le_atom(lm, lc, rm, rc, False))
            elif op == "<":
                parts.append(le_atom(lm, lc, rm, rc, True))
            elif op == ">=":
                parts.append(le_atom(rm, rc, lm, lc, False))
            elif op == ">":
                parts.append(le_atom(rm, rc, lm, lc, True))
            else:
                parts.append(("and", [le_atom(lm, lc, rm, rc, False), le_atom(rm, rc, lm, lc, False)]))
        f = ("and", parts)
        if pos:
            return f
        if op == "=":
            flags.add("disequality")
        return negate(f)
    flags.add(f"op {op}")
    return ("lit", ("odd", op))


def negate(f):
    if f[0] == "lit":
        a = f[1]
        if a[0] == "b":
            return ("lit", ("b", a[1], not a[2]))
        if a[0] == "le":
            return ("lit", neg_le(a))
        return f
    return ("or" if f[0] == "and" else "and", [negate(x) for x in f[1]])


CAP = 4000


class TooBig(Exception):
    pass


def cnf(f):
    """A list of clauses, each a frozenset of atoms; TooBig past CAP clauses."""
    if f[0] == "lit":
        return [frozenset([f[1]])]
    if f[0] == "and":
        out = []
        for x in f[1]:
            out.extend(cnf(x))
            if len(out) > CAP:
                raise TooBig()
        return out
    acc = [frozenset()]
    for x in f[1]:
        cs = cnf(x)
        if len(acc) * len(cs) > CAP:
            raise TooBig()
        acc = [a | c for a in acc for c in cs]
        if len(acc) > CAP:
            raise TooBig()
    return acc


def simplify(clauses):
    """Drop tautologies (x ≤ d ∨ x ≥ d + 1, b ∨ ¬b), duplicates and subsumed clauses."""
    out = []
    for c in set(clauses):
        taut = False
        for a in c:
            if a[0] == "b" and ("b", a[1], not a[2]) in c:
                taut = True
            if a[0] == "le":
                n = neg_le(a)
                if any(b[0] == "le" and b[1] == n[1] and b[2] >= n[2] for b in c):
                    taut = True
        if not taut:
            out.append(c)
    out.sort(key=len)
    kept = []
    for c in out:
        if not any(k <= c for k in kept):
            kept.append(c)
    return kept


def coprime(coef):
    g = 0
    for _, a in coef:
        g = math.gcd(g, a)
    return sorted(abs(a) // g for _, a in coef)


def shape_unit(a, tm, multi):
    """A unit linear literal against the templates: (covered, class)."""
    if a[0] == "b":
        return True, "bound"
    if a[0] == "odd":
        return False, a[1]
    k, cs = len(a[1]), coprime(a[1])
    if k == 1:
        return True, "bound"
    if k == 2:
        ok = all(c in (tm["mags"] if tm["two"] == "mags" else [1]) for c in cs)
        return (True, "two values") if ok else (False, "coefficients outside the template")
    if k == 3:
        if all(c == 1 for c in cs):
            return True, "three values, ±1" + (" (a counterexample's forms)" if multi else "")
        if not multi and tm["three"] == "mags" and all(c in tm["mags"] for c in cs):
            return True, "three values"
        return False, "three values, coefficients outside the template"
    return False, "more than three values in one atom"


def cond_ok(a):
    """A counterexample form's condition: one value, or a sum or difference of two, ±1."""
    if a[0] != "le":
        return False
    cs = sorted(c for _, c in a[1])
    return len(cs) == 1 or cs in ([-1, 1], [1, 1])


def body_ok(a, tm):
    if a[0] != "le":
        return False
    k, cs = len(a[1]), coprime(a[1])
    return k == 1 or (k == 2 and all(c in tm["mags"] for c in cs)) or (k == 3 and all(c == 1 for c in cs))


def shape_clause(c, tm, multi):
    lits = list(c)
    odd = [a for a in lits if a[0] == "odd"]
    if odd:
        return False, odd[0][1]
    if not lits:
        return True, "unreachable"
    if len(lits) == 1:
        return shape_unit(lits[0], tm, multi)
    wide = [a for a in lits if a[0] == "le" and len(a[1]) > 3]
    if wide:
        return False, "more than three values in one atom"
    if len(lits) >= 3:
        return False, "a disjunction of three or more"
    a, b = lits
    if a[0] == "b" or b[0] == "b":
        other = b if a[0] == "b" else a
        if other[0] == "b":
            return True, "a yes/no guard"
        ok, cls = shape_unit(other, tm, multi)
        return (ok and len(other[1]) <= 2), ("a yes/no guard" if ok and len(other[1]) <= 2 else "a yes/no guard on " + cls if not ok else "a yes/no guard on three values")
    if (cond_ok(neg_le(a)) and body_ok(b, tm)) or (cond_ok(neg_le(b)) and body_ok(a, tm)):
        return True, "a disjunction of two (a counterexample's form)"
    return False, "a disjunction of two, outside the counterexample's forms"


ORDER = ["product", "nonlinear", "mod", "div", "modular", "quantified", "ite", "boolean structure past 4,000 clauses",
         "more than three values in one atom", "a disjunction of three or more",
         "a disjunction of two, outside the counterexample's forms", "three values, coefficients outside the template",
         "coefficients outside the template", "a yes/no guard on coefficients outside the template",
         "a yes/no guard on three values", "a disjunction of two (a counterexample's form)",
         "three values, ±1 (a counterexample's forms)", "three values, ±1", "three values", "two values", "a yes/no guard", "bound", "unreachable", "true"]


def rank(cls):
    for i, o in enumerate(ORDER):
        if cls.startswith(o):
            return i
    return 0


def show(a, names):
    """An atom in gdp-wired's slot names (i0.. the Int arguments in order, b0.. the Bool ones)."""
    if a[0] == "b":
        return ("" if a[2] else "not ") + names.get(a[1], a[1])
    if a[0] == "odd":
        return f"<{a[1]}>"
    pos = sorted(((names.get(v, v), c) for v, c in a[1] if c > 0))
    neg = sorted(((names.get(v, v), -c) for v, c in a[1] if c < 0))
    term = lambda ts: " + ".join((f"{c}·{v}" if c != 1 else v) for v, c in ts)
    d = a[2]
    left = term(pos) + (f" + {-d}" if d < 0 and pos else "") if pos else (str(-d) if d < 0 else "0")
    right = term(neg) + (f" + {d}" if d > 0 and neg else "") if neg else (str(d) if d > 0 else "0")
    if d < 0 and not pos:
        left = str(-d)
    if d > 0 and not neg:
        right = str(d)
    return f"{left} <= {right}"


def classify_model(text, tm, preds):
    """Per predicate: its clauses and their classes; the task's classes."""
    sx = parse(text)
    if not sx or sx[0] != "sat" or len(sx) < 2:
        return None
    defs = [d for d in sx[1] if isinstance(d, list) and d and d[0] == "define-fun"]
    nontrivial = [d for d in defs if d[2] and d[4] != "true"]
    multi = len(preds) > 1
    out = {"preds": {}, "classes": collections.Counter(), "flags": set(), "clauses": 0, "nontrivial": 0, "outside": []}
    for d in defs:
        name, params, body = d[1], d[2], d[4]
        if not params:
            continue
        sorts = {p[0]: p[1] for p in params}
        names, k = {}, {"Int": 0, "Bool": 0}
        for q in params:
            names[q[0]] = f"{'i' if q[1] == 'Int' else 'b'}{k[q[1]]}"
            k[q[1]] = k.get(q[1], 0) + 1
        flags = set()
        try:
            f = nnf(body, True, sorts, {}, flags, frozenset())
            cs = simplify(cnf(f))
        except TooBig:
            out["flags"] |= flags | {"big"}
            out["classes"]["boolean structure past 4,000 clauses"] += 1
            out["preds"][name] = {"clauses": None}
            out["nontrivial"] += 1
            continue
        out["flags"] |= flags
        if not cs:
            continue
        out["nontrivial"] += 1
        out["clauses"] += len(cs)
        mine = []
        for c in cs:
            ok, cls = shape_clause(c, tm, multi)
            out["classes"][cls] += 1
            mine.append(cls)
            if not ok:
                lin = [a for a in c if a[0] == "le"]
                out["outside"].append({"cls": cls, "bools": sum(1 for a in c if a[0] == "b"), "linear": len(lin),
                                       "width": max((len(a[1]) for a in lin), default=0),
                                       "coef": max((x for a in lin for x in coprime(a[1])), default=0)})
        out["preds"][name] = {"clauses": len(cs), "classes": dict(collections.Counter(mine)),
                              "inv": [" or ".join(sorted(show(a, names) for a in c)) or "false" for c in cs[:40]]}
    worst = min(out["classes"], key=rank) if out["classes"] else "true"
    out["worst"] = worst
    out["classes"] = dict(out["classes"])
    out["flags"] = sorted(out["flags"])
    return out


def disj(r):
    cs = [o for o in r["outside"] if o["cls"] == "a disjunction of three or more"]
    nl, nb = max(o["linear"] for o in cs), max(o["bools"] for o in cs)
    if nl <= 1 and max(o["width"] for o in cs) <= 2:
        return "yes/no values beside at most one linear literal (of at most two values)"
    if nl == 2:
        return "two linear literals" + (" and yes/no values" if nb else "")
    return "three or more linear literals"


def wide(r):
    cs = [o for o in r["outside"] if o["width"] > 3]
    w, c = max(o["width"] for o in cs), max(o["coef"] for o in cs if o["width"] > 3)
    return f"{'4' if w == 4 else '5-6' if w <= 6 else '7+'} values, " + ("±1" if c == 1 else "a coefficient of 2 or more") + (", in a disjunction" if any(o["linear"] + o["bools"] > 1 for o in cs) else "")


def load(path):
    return [json.loads(l) for l in open(path) if l.strip()]


def solved_set(rows, votes, tool):
    return {r["task"] for r in rows if r["tool"] == tool and r["answer"] in ("sat", "unsat") and (votes.get(r["task"]) is None or r["answer"] == r["expected"])}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gdp", required=True)
    ap.add_argument("--others", required=True)
    ap.add_argument("--models", required=True)
    ap.add_argument("--template", required=True)
    ap.add_argument("--cex")
    ap.add_argument("--given")
    ap.add_argument("--write-given-models", help="write {smt2 path: Spacer's model} of the sat gap's tasks here, for --tools given")
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    votes = {t["task"]: t["vote"] for t in json.load(open(f"{a.gdp}/tasks.json"))}
    gdp = [r for r in load(f"{a.gdp}/results.jsonl") if r["tool"] == "gdp"]
    others = [r for r in load(f"{a.others}/results.jsonl") if r["tool"] != "gdp"]
    mine = solved_set(gdp, votes, "gdp")
    z3 = {r["task"]: r for r in others if r["tool"] == "z3"}
    tmpl = {r["task"]: r["stages"][-1] for r in load(f"{a.template}/results.jsonl") if r.get("stages")}
    models = {r["task"]: r["model"] for r in load(f"{a.models}/models.jsonl")}
    g = {r["task"]: r for r in gdp}

    def stop(r):
        if r is None:
            return "no row"
        st = [s for s in r.get("stages", []) if s.get("stage") != "answer"]
        last = st[-1]["stage"] if st else "nothing"
        h = next((s for s in reversed(st) if s.get("stage") == "houdini"), None)
        if r["answer"] == "timeout":
            return f"timeout after {last}"
        if h and not h.get("proven"):
            why = h.get("why", "")
            m = re.match(r"^(.*) @(\S+)(?: \d+ steps)? (\S+)$", why)
            if not m:
                return "unknown: " + (why or "no goal")
            goal, stuck = m.group(1), m.group(3)
            whose = "the law" if goal == "no clause derives false" else "a candidate"
            return f"unknown: {whose}'s step goal " + ("refuted at a state no candidate rules out (sat)" if stuck == "sat" else f"undecided ({stuck})")
        return f"{r['answer']} after {last}"

    given_rows = load(f"{a.given}/results.jsonl") if a.given else []
    given = {r["task"]: r["stages"][-1] for r in given_rows if r.get("stages")}
    tried = {r["task"] for r in given_rows}

    def given_of(t):
        gv = given.get(t)
        if gv is None:
            return "not proven: out of the 60 s" if t in tried else None
        if gv.get("unstated"):
            return "a conjunct gdp-wired can't state here (" + ", ".join(gv.get("unstatedWhy", [])) + ")"
        if gv.get("proven") and gv.get("checked"):
            return "proven"
        if gv.get("why") == "no model":
            return "no model"
        if "goal" not in gv:
            return "not proven: out of time"
        whose = "the law's" if gv["goal"].startswith("no clause derives false") else "an invariant conjunct's"
        why = gv.get("why", "")
        budget = ", the 200,000-node budget" if "200,000-node" in why else ", the time budget" if "time budget" in why else ""
        left = f" ({gv['nullaryLeftOut']} nullary left out)" if gv.get("nullaryLeftOut") else ""
        return f"not proven: {whose} goal " + ("refuted (sat)" if gv.get("stuck") == "sat" else f"undecided ({gv.get('stuck')}{budget})") + left

    sat_gap = sorted(t for t, r in z3.items() if r["answer"] == "sat" and (votes.get(t) is None or r["expected"] == "sat") and t not in mine)
    if a.write_given_models:
        smt2 = {t["task"]: t["smt2"] for t in json.load(open(f"{a.gdp}/tasks.json"))}
        json.dump({smt2[t]: models[t] for t in sat_gap if models.get(t, "").startswith("sat")}, open(a.write_given_models, "w"))
        json.dump([t for t in sat_gap if models.get(t, "").startswith("sat")], open(a.write_given_models.replace(".json", "-tasks.json"), "w"))
    rows = {}
    for t in sat_gap:
        m = models.get(t)
        tm = tmpl.get(t)
        hz = next((x for x in reversed(g.get(t, {}).get("stages", [])) if x.get("stage") == "houdini"), {})
        row = {"task": t, "kind": "sat", "gdp": stop(g.get(t)), "gdp_answer": g.get(t, {}).get("answer"), "why": hz.get("why"), "seconds": g.get(t, {}).get("seconds")}
        if tm is None:
            row["class"] = "no template row"
        elif m is None or not m.startswith("sat"):
            row["class"] = "no Spacer model in 60 s"
        else:
            row["template"] = {k: tm[k] for k in ("P", "mags", "two", "three", "nInt", "nBool")}
            row["given"] = given_of(t)
            if t in given:
                row["given_ms"] = given[t].get("proveMs")
            row["npreds"] = len(tm["preds"])
            c = classify_model(m, tm, tm["preds"])
            if c is None:
                row["class"] = "model unreadable"
            else:
                row.update(c)
                row["class"] = c["worst"]
        rows[t] = row

    unsat_gap = sorted(t for t in {r["task"] for r in others} if t not in mine and any(r["task"] == t and r["answer"] == "unsat" and (votes.get(t) is None or r["expected"] == "unsat") for r in others))
    cex = {r["task"]: r["model"] for r in load(f"{a.cex}/models.jsonl")} if a.cex else {}
    for t in unsat_gap:
        r = g.get(t)
        w = cex.get(t, "")
        steps = None
        if w.startswith("unsat"):
            lines = [l for l in w.splitlines() if re.match(r"^\d+:", l)]
            steps = len([l for l in lines if "->" in l])
        guided = next((s for s in (r or {}).get("stages", []) if s.get("stage") == "guided"), None)
        runs = next((s for s in (r or {}).get("stages", []) if s.get("stage") == "runs"), None)
        row = {"task": t, "kind": "unsat", "gdp": stop(r), "gdp_answer": (r or {}).get("answer"), "cex": steps,
               "runs": bool(runs), "guided_steps": guided.get("steps") if guided else None, "guided_trials": guided.get("trials") if guided else None}
        depth = guided["steps"] / guided["trials"] if guided and guided.get("trials") else 0
        row["guided_depth"] = round(depth, 1)
        if steps is None:
            row["class"] = "no Golem derivation in 60 s"
        elif not guided:
            row["class"] = "the runs never ran (" + row["gdp"] + ")"
        elif steps > 2000:
            row["class"] = "a derivation past 2,000 steps (a guided run's cap)"
        elif steps > depth:
            row["class"] = "a derivation longer than the guided runs go (their steps per trial)"
        else:
            row["class"] = "a derivation within the guided runs' depth, its values not found"
        rows[t] = row

    for r in rows.values():
        if r.get("class") == "a disjunction of three or more":
            r["sub"] = disj(r)
        elif r.get("class") == "more than three values in one atom":
            r["sub"] = wide(r)
    json.dump(rows, open(a.out, "w"), indent=1, default=list)
    sat_rows = [r for r in rows.values() if r["kind"] == "sat"]
    un_rows = [r for r in rows.values() if r["kind"] == "unsat"]
    print(f"sat: {len(sat_rows)} tasks Spacer answers sat and gdp-wired doesn't solve")
    for k, n in collections.Counter(r["class"] for r in sat_rows).most_common():
        print(f"  {n:4}  {k}")
    print("  any clause of the class (a task counts once per class):")
    any_cls = collections.Counter(c for r in sat_rows for c in r.get("classes", {}))
    for k, n in any_cls.most_common():
        print(f"  {n:4}  {k}")
    print("  flags:", collections.Counter(f for r in sat_rows for f in r.get("flags", [])).most_common())
    cl = [r["clauses"] for r in sat_rows if "clauses" in r]
    print("  clauses per task:", collections.Counter("0" if c == 0 else "1-3" if c <= 3 else "4-10" if c <= 10 else "11-30" if c <= 30 else ">30" for c in cl).most_common())
    print("  predicates with a nontrivial interpretation:", collections.Counter(min(r.get("nontrivial", 0), 4) for r in sat_rows if "nontrivial" in r).most_common())
    print("  a disjunction of three or more, by its literals (the task's widest such clause):")
    for k, n in collections.Counter(disj(r) for r in sat_rows if r["class"] == "a disjunction of three or more").most_common():
        print(f"  {n:4}  {k}")
    print("  more than three values in one atom, by the widest atom and its coefficients:")
    for k, n in collections.Counter(wide(r) for r in sat_rows if r["class"] == "more than three values in one atom").most_common():
        print(f"  {n:4}  {k}")
    if given:
        print("  given Spacer's invariant, proveRule (no search), per class:")
        for k, n in sorted(collections.Counter((r["class"], r.get("given")) for r in sat_rows if r.get("given")).items(), key=lambda kv: -kv[1]):
            print(f"  {n:4}  {k[0]} | {k[1]}")
        print("  given, overall:", collections.Counter(r.get("given") for r in sat_rows if "given" in r).most_common())
    print("  by gdp-wired's stop, per class:")
    for k, n in collections.Counter((r["class"], r["gdp"]) for r in sat_rows).most_common():
        print(f"  {n:4}  {k[0]} | {k[1]}")
    print(f"unsat: {len(un_rows)} tasks another tool answers unsat and gdp-wired doesn't")
    for k, n in collections.Counter(r["class"] for r in un_rows).most_common():
        print(f"  {n:4}  {k}")


if __name__ == "__main__":
    main()
