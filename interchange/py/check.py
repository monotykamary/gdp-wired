"""A second checker for interchange documents, written from the specification (docs/interchange.md) in Python, with
nothing shared with the TypeScript kernel but the format: the tree and derivation check of a `goals` document (the
kernel's `check`, core/check.ts's `checkRefutation`). A goal is hypotheses over naturals that can't all hold; its tree
splits on linear atoms, and each leaf's derivation must refute the rows the hypotheses give under the leaf's path.

    python3 check.py [--json] <goals.json>...

Prints each goal's verdict (accepted or refused); with --json, one JSON list per file of [name, accepted]. Exit 0
when every goal is accepted, 1 otherwise. The rest of a certificate (how a rule's goals are built, a stem evaluated,
a cyclic proof's ranks) is the TypeScript checker's; `gdp-wired-check --goals` writes any certificate's goals.

Numbers are exact (Python integers); a row whose coefficient leaves the safe integers (|n| > 2^53 - 1), where the
reference computes in doubles, is refused, as the format leaves that range out.
"""
import json
import re
import sys

SAFE = 2 ** 53 - 1


class Refused(Exception):
    pass


def safe(n):
    if abs(n) > SAFE:
        raise Refused("a number past 2^53 - 1")
    return n


# --- linear forms: a dict, the constant under '1', listed first (as a JavaScript object lists an index key first) ---
def keys(lin):
    if "1" in lin:
        yield "1"
    for key in lin:
        if key != "1":
            yield key


def add(*xs):
    out = {}
    for x in xs:
        for key in keys(x):
            out[key] = safe(out.get(key, 0) + x[key])
    for key in list(keys(out)):
        if out[key] == 0:
            del out[key]
    return out


def scale(x, f):
    out = {}
    for key in keys(x):
        value = safe(x[key] * f)
        if value != 0:
            out[key] = value
    return out


def sub(a, b):
    out = {}
    for key in keys(a):
        out[key] = a[key]
    for key in keys(b):
        out[key] = safe(out.get(key, 0) - b[key])
    for key in list(keys(out)):
        if out[key] == 0:
            del out[key]
    return out


def k(value):
    return {} if value == 0 else {"1": value}


def v(name):
    return {name: 1}


def utf16(s):
    # JavaScript sorts strings by UTF-16 code units
    return s.encode("utf-16-be")


def canon(lin):
    return ",".join(f"{key}:{lin[key]}" for key in sorted(lin, key=utf16))


def canon_flip(lin):
    ks = list(lin) + ([] if "1" in lin else ["1"])
    parts = []
    for key in sorted(ks, key=utf16):
        c = 1 - lin.get("1", 0) if key == "1" else -lin[key]
        if c != 0:
            parts.append(f"{key}:{c}")
    return ",".join(parts)


def decide(lin, path):
    if all(key == "1" for key in lin):
        return lin.get("1", 0) <= 0
    d = path.get(canon(lin))
    if d is not None:
        return d[1]
    f = path.get(canon_flip(lin))
    return None if f is None else not f[1]


# --- term columns: a choice a path leaves open, named by its term (interned by structure) -----------------------------
TERMS = {}
TABLE = []


def column(e):
    key = json.dumps(e, sort_keys=True, separators=(",", ":"))
    i = TERMS.get(key)
    if i is None:
        i = TERMS[key] = len(TABLE)
        TABLE.append(e)
    return f"⟦{i}⟧"


def column_term(name):
    m = re.fullmatch(r"⟦(\d+)⟧", name)
    return TABLE[int(m.group(1))] if m else None


def factors(name):
    out, depth, start = [], 0, 0
    for i in range(len(name) + 1):
        ch = name[i] if i < len(name) else None
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        elif (ch == "*" and depth == 0) or ch is None:
            out.append(name[start:i])
            start = i + 1
    return out


def is_monomial(name):
    return len(factors(name)) > 1


def is_cell(name):
    return "[" in name and not is_monomial(name)


def times(a, b):
    out = []
    for p in keys(a):
        for q in keys(b):
            if "⟦" in p or "⟦" in q:
                return None
            fs = sorted((factors(p) if p != "1" else []) + (factors(q) if q != "1" else []), key=utf16)
            out.append({"*".join(fs) if fs else "1": safe(a[p] * b[q])})
    return add(*out)


RESERVED = re.compile(r"[*\[\],:⟦]")


def linear(e, path):
    op = e["op"]
    if op == "var":
        return None if e["name"] == "1" or RESERVED.search(e["name"]) else v(e["name"])
    if op == "const":
        return k(e["value"])
    if op == "mul":
        a = linear(e["a"], path)
        return None if a is None else scale(a, e["k"])
    if op == "prod":
        a, b = linear(e["a"], path), linear(e["b"], path)
        return None if a is None or b is None else times(a, b)
    if op == "add":
        a, b = linear(e["a"], path), linear(e["b"], path)
        return None if a is None or b is None else add(a, b)
    if op in ("sub", "min", "max"):
        a, b = linear(e["a"], path), linear(e["b"], path)
        if a is None or b is None:
            return None
        a_le_b, b_le_a = decide(sub(a, b), path), decide(sub(b, a), path)
        if op == "sub":
            return sub(a, b) if b_le_a is True else k(0) if b_le_a is False else v(column(e))
        if a_le_b is None:
            return v(column(e))
        return a if (op == "min") == a_le_b else b
    if op == "if":
        c = truth(e["c"], path)
        return v(column(e)) if c is None else linear(e["then"] if c else e["else"], path)
    if op == "get":
        key = linear(e["key"], path)
        return None if key is None else v(f"{e['map']}[{canon(key)}]")
    raise Refused(f"no term op {op}")


def decided(e, path):
    if e["op"] == "if":
        return truth(e["c"], path) is not None
    if e["op"] not in ("sub", "min", "max"):
        return True
    a, b = linear(e["a"], path), linear(e["b"], path)
    return a is not None and b is not None and decide(sub(b, a) if e["op"] == "sub" else sub(a, b), path) is not None


def term_rows(name, path):
    e, col, out = column_term(name), v(name), []
    if e["op"] in ("min", "max", "sub"):
        a, b = linear(e["a"], path), linear(e["b"], path)
        if a is not None and b is not None:
            if e["op"] == "min":
                out += [sub(col, a), sub(col, b)]
            if e["op"] == "max":
                out += [sub(a, col), sub(b, col)]
            if e["op"] == "sub":
                out += [sub(sub(a, b), col), sub(col, a)]
    if e["op"] == "if":
        a, b = linear(e["then"], path), linear(e["else"], path)
        const = lambda l: all(key == "1" or c == 0 for key, c in l.items())
        if a is not None and b is not None and const(a) and const(b):
            out.append(sub(col, add(a, b)))
    if decided(e, path):
        r = linear(e, path)
        if r is not None:
            out += [sub(col, r), sub(r, col)]
    return out


def comparison(c, path):
    a, b = linear(c["a"], path), linear(c["b"], path)
    if a is None or b is None:
        return None
    ab, ba = sub(a, b), sub(b, a)
    if c["op"] == "<=":
        return [ab], [[add(ba, k(1))]]
    if c["op"] == "<":
        return [add(ab, k(1))], [[ba]]
    return [ab, ba], [[add(ab, k(1))], [add(ba, k(1))]]


def truth(c, path):
    op = c["op"]
    if op == "flag":
        raise Refused("a flag (inlined before a goal is made)")
    if op == "all":
        return None
    if op == "not":
        t = truth(c["x"], path)
        return None if t is None else not t
    if op in ("and", "or"):
        ts, dominant = [truth(y, path) for y in c["xs"]], op == "or"
        if any(t is dominant for t in ts):
            return dominant
        return (not dominant) if all(t is (not dominant) for t in ts) else None
    cmp = comparison(c, path)
    if cmp is None:
        return None
    ts = [decide(lin, path) for lin in cmp[0]]
    if any(t is False for t in ts):
        return False
    return True if all(t is True for t in ts) else None


def facts(c, path, positive=True):
    op = c["op"]
    if op == "flag":
        raise Refused("a flag (inlined before a goal is made)")
    if op == "all":
        return []
    if op == "not":
        return facts(c["x"], path, not positive)
    if op in ("and", "or"):
        if (op == "and") == positive:
            return [lin for y in c["xs"] for lin in facts(y, path, positive)]
        opened = [y for y in c["xs"] if truth(y, path) is not (not positive)]
        return [k(1)] if not opened else facts(opened[0], path, positive) if len(opened) == 1 else []
    cmp = comparison(c, path)
    if cmp is None:
        return []
    if positive:
        return cmp[0]
    opened = [atoms for atoms in cmp[1] if not any(decide(lin, path) is False for lin in atoms)]
    return [k(1)] if not opened else opened[0] if len(opened) == 1 else []


def key_of(cell):
    inner, out, depth, start = cell[cell.index("[") + 1:-1], {}, 0, 0
    for i in range(len(inner) + 1):
        ch = inner[i] if i < len(inner) else None
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
        elif (ch == "," and depth == 0) or ch is None:
            if i > start:
                part = inner[start:i]
                j = part.rindex(":")
                out[part[:j]] = int(part[j + 1:])
            start = i + 1
    return out


def leaf_rows(hyps, path):
    rows = [lin if holds else add(k(1), scale(lin, -1)) for lin, holds in path.values()]
    for h in hyps:
        rows += facts(h, path)
    names = {}
    for r in rows:
        for key in keys(r):
            if key != "1":
                names[key] = True
    cells = [(n, n[:n.index("[")], key_of(n)) for n in names if is_cell(n)]
    for i, (p, pm, pk) in enumerate(cells):
        for q, qm, qk in cells[i + 1:]:
            if pm != qm:
                continue
            d = sub(pk, qk)
            if decide(d, path) is True and decide(scale(d, -1), path) is True:
                rows += [sub(v(p), v(q)), sub(v(q), v(p))]
    seen, todo = set(), [n for n in names if n.startswith("⟦")]
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        for lin in term_rows(name, path):
            rows.append(lin)
            for key in keys(lin):
                if key != "1":
                    names[key] = True
                    if key.startswith("⟦") and key not in seen:
                        todo.append(key)
    rows += [{name: -1} for name in names]
    return rows


def with_products(rows, pairs, squares):
    out = list(rows)
    for t in squares:
        tt = times(t, t)
        out.append({} if tt is None else scale(tt, -1))
    for i, j in pairs:
        p = out[i] if 0 <= i < len(out) else None
        q = out[j] if 0 <= j < len(out) else None
        pq = times(p, q) if p is not None and q is not None else None
        out.append({} if pq is None else scale(pq, -1))
    return out


def refutes(rows, steps):
    made = []
    for i, s in enumerate(steps):
        if s[0] == "input":
            if not 0 <= s[1] < len(rows):
                return False
            made.append(rows[s[1]])
        elif s[0] == "combine":
            _, a, b, ma, mb = s
            if not (0 <= a < i and 0 <= b < i and ma > 0 and mb > 0):
                return False
            out = {}
            for lin, m in ((made[a], ma), (made[b], mb)):
                for key in keys(lin):
                    out[key] = safe(out.get(key, 0) + m * lin[key])
            made.append(out)
        else:
            _, of, g = s
            if not (0 <= of < i and g > 0):
                return False
            row = made[of]
            if any(row[key] % g != 0 for key in row if key != "1"):
                return False
            out = {"1": -((-row.get("1", 0)) // g)}
            for key in keys(row):
                if key != "1":
                    out[key] = row[key] // g
            made.append(out)
    if not made:
        return False
    last = made[-1]
    return all(last[key] == 0 for key in last if key != "1") and last.get("1", 0) > 0


def check(hyps, tree, path=None):
    path = {} if path is None else path
    if "leaf" in tree:
        return refutes(with_products(leaf_rows(hyps, path), tree.get("products", []), tree.get("squares", [])), tree["leaf"])
    split = tree["split"]
    cid = canon(split)
    if cid in path or all(key == "1" for key in split):
        return False
    return check(hyps, tree["yes"], {**path, cid: (split, True)}) and check(hyps, tree["no"], {**path, cid: (split, False)})


# --- the document: atoms back to the names the check reads --------------------------------------------------------------
def read_tree(t, cols):
    def lin(x):
        out = {}
        if x[0] is not None:
            out["1"] = x[0]
        for c, atom in x[1:]:
            name = atom_name(atom)
            if name in out:
                raise Refused(f"the atom {name} twice")
            out[name] = c
        return out

    def atom_name(a):
        if isinstance(a, str):
            return a
        if "col" in a:
            return column(cols[a["col"]])
        if "mono" in a:
            return "*".join(sorted((atom_name(f) for f in a["mono"]), key=utf16))
        return f"{a['cell']}[{canon(lin(a['key']))}]"

    def tree(x):
        if "split" in x:
            return {"split": lin(x["split"]), "yes": tree(x["yes"]), "no": tree(x["no"])}
        return {"leaf": x["leaf"], "products": x.get("products", []), "squares": [lin(s) for s in x.get("squares", [])]}

    return tree(t)


def check_document(doc):
    if doc.get("format") != "gdp-wired-interchange" or doc.get("version") != "1.0" or doc.get("kind") != "goals":
        raise Refused("a goals document of format 1.0")
    cols, out = doc.get("columns", []), []
    for g in doc["goals"]:
        try:
            ok = check(g["hyps"], read_tree(g["tree"], cols))
        except (Refused, RecursionError, KeyError, IndexError, TypeError, ValueError):
            ok = False
        out.append([g["name"], ok])
    return out


def main(argv):
    as_json = "--json" in argv
    files = [a for a in argv if not a.startswith("--")]
    sys.setrecursionlimit(1 << 16)
    every = True
    for f in files:
        with open(f) as fh:
            res = check_document(json.load(fh))
        every = every and all(ok for _, ok in res)
        if as_json:
            print(json.dumps(res, ensure_ascii=False))
        else:
            for name, ok in res:
                print(f"{'accepted' if ok else 'refused '}  {name}")
    return 0 if every else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
