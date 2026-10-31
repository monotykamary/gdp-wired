"""TLC's state dump (-dump) of learning_switch against check.ts --dump's projected states: the states on one side only.
    python3 dumpdiff.py <tlc dump> <check dump>"""
import itertools, json, re, sys

def node(s): return int(s.strip()[1:]) - 1
def states(path):
    text = open(path).read()
    for block in re.split(r"\nState \d+:\s*\n", "\n" + text)[1:]:
        tab = re.search(r"table = \{(.*?)\}", block, re.S).group(1)
        pen = re.search(r"pending = \{(.*?)\}", block, re.S).group(1)
        T = {tuple(node(x) for x in m.split(",")) for m in re.findall(r"<<(.*?)>>", tab)}
        P = {tuple(node(x) for x in m.split(",")) for m in re.findall(r"<<(.*?)>>", pen)}
        r3 = range(3)
        yield json.dumps([[1 if (t, x, y) in T else 0 for t in r3 for x in r3 for y in r3],
                          [1 if (a, b, c, d) in P else 0 for a in r3 for b in r3 for c in r3 for d in r3]], separators=(",", ":"))
tlc = set(states(sys.argv[1]))
port = {json.dumps(json.loads(l), separators=(",", ":")) for l in open(sys.argv[2]) if l.strip()}
print(json.dumps({"tlc": len(tlc), "port": len(port), "tlc_only": len(tlc - port), "port_only": len(port - tlc)}))
def show(s):
    t, p = json.loads(s); r3 = range(3)
    T = [k for k, v in zip(itertools.product(r3, r3, r3), t) if v and k[1] != k[2]]
    P = [k for k, v in zip(itertools.product(r3, r3, r3, r3), p) if v]
    return f"table+{T} pending {P}"
for s in sorted(tlc - port, key=len)[:4]: print("tlc only:", show(s))
for s in sorted(port - tlc, key=len)[:4]: print("port only:", show(s))
