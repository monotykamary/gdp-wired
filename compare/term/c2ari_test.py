"""Adversarial C programs (adversarial/*.c.txt: from the independent check of the ranks, research/verify-ranks on
verify/ranks; the C front end's own; and v_*, from the independent check of the C front end, research/verify-sv on
verify/sv-front: static locals, objects a pointer names later in the text, overflow on the side && and || don't
evaluate, constant indices, enum types, the preprocessor, unspecified evaluation order, a reach_error that returns, a
goto past a declaration; v2_*, from its re-check: a dereference beside a call writing what it may read, comments
read as the lexer reads them, trigraphs and a spliced backslash-space): conversions to char, short and _Bool, unsigned arithmetic, the usual
arithmetic conversions, the data model, recursion (globals and values across calls, calls that never return, depth
past the inlining), arrays (an index that is not a constant, large arrays), pointers (aliases, malloc'd cells, free),
division and remainder, the ternary operator, calls inside expressions, and undefined behaviour (where the run ends,
and where it doesn't: the right side of || not evaluated, a ternary's other branch). Each is one of:

  - "expect: nonterminating": it runs forever; it must never be answered terminates;
  - "expect: terminates": every run ends (or reaches undefined behaviour); it must never be answered nonterminating.

c2ari.py refuses it, or, translated (a recursive one with --for the answer it must not give), solve.ts searching only
for the answer it must not give (--want) doesn't give it. Each is also searched for its own answer, briefly, and the
count printed (a check of the translation, not of the prover). A first line `// c2ari: data_model=ILP32 no_overflow`
sets the translation's options.

    python3 compare/term/c2ari_test.py        (pycparser 3.0; bun for a program that translates)
"""
import concurrent.futures
import json
import pathlib
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c2ari  # noqa: E402

LIMIT, OWN = 10, 5


def solve(ari, want, limit):
    with tempfile.NamedTemporaryFile("w", suffix=".ari", delete=False) as out:
        out.write(ari)
    p = subprocess.run(["bun", str(HERE / "solve.ts"), out.name, "--limit", str(limit), "--want", want], capture_output=True, text=True, cwd=HERE.parent.parent)
    answers = [json.loads(l).get("answer") for l in p.stdout.splitlines() if l.startswith("{")]
    return next((a for a in reversed(answers) if a), "none")


def probe(f):
    text = f.read_text()
    m = re.search(r"expect: (nonterminating|terminates)", text)
    assert m, f
    expect = m.group(1)
    bad = "terminates" if expect == "nonterminating" else "nonterminating"
    opts = re.search(r"^// c2ari: (.*)$", text, re.M)
    opts = opts.group(1).split() if opts else []
    dm = next((o.split("=")[1] for o in opts if o.startswith("data_model=")), "LP64")
    no_overflow = "no_overflow" in opts
    out = {}
    for mode, want in ((bad, bad), (expect, expect)):
        try:
            try:
                prog, start = c2ari.translate(text, dm, no_overflow, None)
            except c2ari.Refused as e:
                if not str(e).startswith("recursion"):
                    raise
                prog, start = c2ari.translate(text, dm, no_overflow, mode)
        except c2ari.Refused as e:
            return f.name, expect, f"refused ({e})", None
        out[want] = solve(c2ari.emit(prog, start), want, LIMIT if want == bad else OWN)
    return f.name, expect, out[bad], out[expect]


probes = sorted((HERE / "adversarial").glob("*.c.txt"))  # (.c.txt: a batch's tree leaves out *.c)
assert len(probes) >= 30, probes
failed, own = [], 0
with concurrent.futures.ThreadPoolExecutor(2) as ex:
    for name, expect, got, mine in ex.map(probe, probes):
        bad = "terminates" if expect == "nonterminating" else "nonterminating"
        print(f"{name}: expect {expect}; searched for {bad}: {got}" + (f"; for {expect}: {mine}" if mine else ""), flush=True)
        if got == bad:
            failed.append(name)
        own += mine == expect
if failed:
    print("answered against the program:", failed)
    sys.exit(1)
print(f"{len(probes)} programs, none answered against the program; {own} answered as they run")
