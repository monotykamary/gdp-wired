"""The two disputed labels (compare/chc/disputed.json), checked with no gdp-wired code: each task's clauses written out
by hand from its .smt2, the derivation file (research/bmc2/derivation.ts) replayed on them step by step, every head
value compared, and the query checked at the end. `python3 research/bmc2/disputed.py <derivation.json.gz>...`"""
import gzip, json, sys

# s_split_50: inv(D C B A) from D = C = B = A = 0; inv(F H G E) -> inv(D C B A) with C = H + 1, B = ite(1000 <= F, G, G + 1),
# A = ite(F >= 1000, E + 1, E), D = (F + 1) mod 2000; query inv(D C B A), C = 999000, B - A = 1000.
def split50(s):
    if s is None: return (0, 0, 0, 0)
    F, H, G, E = s
    return ((F + 1) % 2000, H + 1, G if 1000 <= F else G + 1, E + 1 if F >= 1000 else E)
def query50(s): return s[1] == 999000 and s[2] - s[3] == 1000
# s_split_22: inv(C B A) from B = 767976, A = 0, C = 0; inv(F E D) -> inv(C B A) with B = E - 1, A = ite((F - E) mod 3 = 1,
# D + 3, D), C = F + 1; query inv(B C A) (first argument B, third A), A >= 280275, B >= 280275.
def split22(s):
    if s is None: return (0, 767976, 0)
    F, E, D = s
    return (F + 1, E - 1, D + 3 if (F - E) % 3 == 1 else D)
def query22(s): return s[2] >= 280275 and s[0] >= 280275
TASKS = {"s_split_50_000.smt2": (split50, query50), "s_split_22_000.smt2": (split22, query22)}

for path in sys.argv[1:]:
    doc = json.loads(gzip.decompress(open(path, "rb").read()))
    step, query = next(v for k, v in TASKS.items() if doc["task"].endswith(k))
    st, n = None, 0
    for s in doc["derivation"][:-1]:
        st = step(st); n += 1
        got = tuple(s["after"][f"i{k}"] for k in range(len(st)))
        assert got == st, (n, got, st)
    assert doc["derivation"][-1]["after"]["loc"] == "error" and query(st), "the last step's query does not hold"
    print(f"{doc['task']}: {doc['steps']} steps replayed on the clauses written by hand, every head value the same, the query holds at the end ({st})")
