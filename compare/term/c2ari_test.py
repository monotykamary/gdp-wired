"""Adversarial C programs (adversarial/*.c, from the independent check of the ranks, research/verify-ranks on
verify/ranks, and one more): conversions to char, short and _Bool, which wrap or make 0 or 1 where unbounded integers
would not. Each runs forever ("expect: nonterminating"), and none may be answered terminates: c2ari.py refuses it,
or, translated, solve.ts doesn't answer terminates.

    python3 compare/term/c2ari_test.py        (pycparser 3.0; bun for a program that translates)
"""
import json
import pathlib
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import c2ari  # noqa: E402

failed = []
probes = sorted((HERE / "adversarial").glob("*.c"))
assert len(probes) >= 5, probes
for f in probes:
    text = f.read_text()
    assert "expect: nonterminating" in text, f
    try:
        prog, start = c2ari.translate(text)
    except c2ari.Refused as e:
        print(f"{f.name}: refused ({e})")
        continue
    with tempfile.NamedTemporaryFile("w", suffix=".ari", delete=False) as out:
        out.write(c2ari.emit(prog, start))
    p = subprocess.run(["bun", str(HERE / "solve.ts"), out.name, "--limit", "20"], capture_output=True, text=True, cwd=HERE.parent.parent)
    answers = [json.loads(l).get("answer") for l in p.stdout.splitlines() if l.startswith("{")]
    answer = next((a for a in reversed(answers) if a), "none")
    print(f"{f.name}: translated, {answer}")
    if answer == "terminates":
        failed.append(f.name)
if failed:
    print("answered terminates:", failed)
    sys.exit(1)
print(f"{len(probes)} programs, none answered terminates")
