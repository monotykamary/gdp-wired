"""Two scored runs of the real-world corpus (research/realworld/score.ts --json), law by law: `python3 research/query/rwdiff.py
<here.json> <main.json>`. The outcomes' counts each side, every law whose outcome differs, and the times of the laws
both prove."""
import collections
import json
import sys

a, b = (json.load(open(f)) for f in sys.argv[1:3])
key = lambda r: (r["item"], r["law"])
A, B = {key(r): r for r in a}, {key(r): r for r in b}
print("here", dict(collections.Counter(r["outcome"] for r in a)), "main", dict(collections.Counter(r["outcome"] for r in b)))
diff = [(k, A[k]["outcome"], B[k]["outcome"], A[k].get("ms"), B[k].get("ms")) for k in sorted(A) if k in B and A[k]["outcome"] != B[k]["outcome"]]
print(f"{len(diff)} laws differ")
for d in diff: print("  ", *d)
both = [(A[k]["ms"], B[k]["ms"]) for k in A if k in B and A[k]["outcome"] == B[k]["outcome"] == "proven"]
if both:
    import statistics
    print(f"proven on both: {len(both)}; summed ms here {sum(x for x, _ in both)}, main {sum(y for _, y in both)}; median ratio {statistics.median(x / max(1, y) for x, y in both):.3f}")
