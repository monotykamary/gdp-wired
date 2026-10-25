"""TIP (Tons of Inductive Problems) on Modal: gdp-wired's proveData (solve.ts) beside cvc5's and Vampire's induction,
each task in its own container (2 vCPU, 4 GB) under the same wall-clock limit for every tool, all at once (`starmap`).

    modal run compare/tip/modal_tip.py --out runs/modal/tip/<name> [--tools gdp,cvc5,cvc5cg,vampire] [--limit 60]
                                       [--sets isaplanner,prod,tip2015,grammars] [--only <substring>|<substring>]
                                       [--sample 0] [--per 1] [--probe-only]

The benchmarks are tip-org/benchmarks at a pinned commit, fetched into the image; cvc5 and Vampire read them as the TIP
tools (tip-org/tools, pinned, built in the image with Stack) translate them: `tip <f> --smtlib` (monomorphised, lambdas
axiomatised, the goal negated: `(assert (not φ)) (check-sat)`) and `tip <f> --vampire` (the same, the goal as
`assert-not`), both made once in the image. gdp-wired reads the TIP file itself (translate.ts). <out>/results.jsonl has
one row per tool and task. The app id and client pid are registered in modal/.live/ (modal/reap.sh stops an orphan); the
app, and every call in it, stops when this entrypoint exits.
"""
import json
import os
import pathlib
import time

try:
    import modal
except ImportError:  # plain python3, --backend boat: the runner's functions run on boat VMs (modal/fanout.py)
    import sys
    sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent.parent.parent / "modal"))
    from agent import modal_stub
    modal = modal_stub()

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
BENCH_COMMIT = "bace5b2f0e45d526ec82ce5de6b25fe024984161"  # tip-org/benchmarks, 2023-07-05
TOOLS_COMMIT = "ca4c414fbca5276c0c0c7af3d5c89df006452938"  # tip-org/tools, 2026-04-15
CVC5 = "1.4.2"
VAMPIRE = "v5.1.0"
SETS = ["isaplanner", "prod", "tip2015", "grammars", "false"]
CONVERT = r"""
import pathlib, subprocess, json
root = pathlib.Path('/bench/benchmarks')
log = {}
for d in %s:
    for f in sorted((root / d).glob('*.smt2')):
        rel = f.relative_to(root)
        for mode, out in (('--smtlib', '/smt'), ('--vampire', '/vamp')):
            dst = pathlib.Path(out) / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            p = subprocess.run(['tip', str(f), mode], capture_output=True, text=True, timeout=120)
            if p.returncode == 0 and p.stdout.strip():
                dst.write_text(p.stdout)
            else:
                log[f'{mode} {rel}'] = (p.stderr or p.stdout)[-400:]
pathlib.Path('/smt/convert-errors.json').write_text(json.dumps(log, indent=1))
print(len(log), 'conversion errors')
""" % json.dumps(SETS)

# TIP writes a match's default case as `_`, which SMT-LIB 2.6 (and cvc5's parser) doesn't take as a pattern: in the cvc5
# files, each such case gets a variable pattern of its own instead (a variable pattern matches every value, as `_` does).
WILD = r"""
import pathlib, re, json
def parse(t):
    out, st = [], [[]]
    for m in re.finditer(r'\s+|;[^\n]*|\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()|;"]+', t):
        x = m.group(0)
        if x[0].isspace() or x[0] == ';': continue
        if x == '(': st.append([])
        elif x == ')': l = st.pop(); st[-1].append(l)
        else: st[-1].append(x)
    return st[0]
n = [0]
def fix(s):
    if not isinstance(s, list): return s
    if s and s[0] == 'match' and len(s) == 3 and isinstance(s[2], list):
        for c in s[2]:
            if isinstance(c, list) and c and c[0] == '_':
                n[0] += 1; c[0] = 'wild_' + str(n[0])
    return [fix(x) for x in s]
def show(s): return s if not isinstance(s, list) else '(' + ' '.join(show(x) for x in s) + ')'
changed = []
for f in sorted(pathlib.Path('/smt').rglob('*.smt2')):
    t = f.read_text()
    if re.search(r'\(\s*_\s', t):
        n[0] = 0
        cmds = [fix(c) for c in parse(t)]
        if n[0]:
            f.write_text('\n'.join(show(c) for c in cmds) + '\n'); changed.append(str(f))
pathlib.Path('/smt/wild-patterns.json').write_text(json.dumps(changed, indent=1))
print(len(changed), 'files with a default case renamed')
"""

image = (
    modal.Image.from_registry("ubuntu:22.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "git", "build-essential", "libtinfo-dev", "libgmp-dev", "zlib1g-dev", "xz-utils", "coreutils", "netbase")
    .run_commands(
        "curl -fsSL https://get.haskellstack.org/ | sh",
        f"git clone https://github.com/tip-org/tools.git /tools && cd /tools && git checkout {TOOLS_COMMIT}",
        "cd /tools && stack --no-terminal setup && stack --no-terminal build tip-lib --copy-bins --local-bin-path /usr/local/bin && tip --help | head -3",
    )
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash -s bun-v1.4.4",
        f"curl -fsSL -o /tmp/cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-{CVC5}/cvc5-Linux-x86_64-static.zip"
        " && unzip -q /tmp/cvc5.zip -d /opt && ln -s $(find /opt -path '*cvc5-Linux-x86_64-static/bin/cvc5') /usr/local/bin/cvc5 && cvc5 --version | head -1",
        f"curl -fsSL -o /tmp/vampire.zip https://github.com/vprover/vampire/releases/download/{VAMPIRE}/vampire-Linux-X64.zip"
        " && mkdir -p /opt/vampire && unzip -q /tmp/vampire.zip -d /opt/vampire && ln -s $(find /opt/vampire -type f -name 'vampire*' | head -1) /usr/local/bin/vampire && chmod +x /usr/local/bin/vampire && vampire --version",
        f"mkdir /bench && curl -fsSL https://codeload.github.com/tip-org/benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /bench --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{CONVERT}\nEOF")
    .run_commands(f"python3 - <<'EOF'\n{WILD}\nEOF")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "modal/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "lean-kernel/**", "research/**", "static/**", "docs/**"])
)
app = modal.App("gdp-wired-tip", image=image)

# The same image on a boat VM, a layer of the pool's snapshot (modal/boat.py): the TIP tools built once, bun 1.4.4
# beside the pool's (first on PATH for each call), the benchmarks under /opt/gdpw/tip mounted at /bench (BOAT).
BOAT_SETUP = f"""
sudo apt-get install -y -q build-essential libtinfo-dev libgmp-dev zlib1g-dev netbase
command -v stack || curl -fsSL https://get.haskellstack.org/ | sh
rm -rf /tmp/tools && git clone -q https://github.com/tip-org/tools.git /tmp/tools && cd /tmp/tools && git checkout -q {TOOLS_COMMIT}
cd /tmp/tools && stack --no-terminal setup && stack --no-terminal build tip-lib --copy-bins --local-bin-path /tmp/tipbin
sudo cp /tmp/tipbin/tip /usr/local/bin/tip && tip --help | head -3
cd ~ && rm -rf /tmp/tools /tmp/tipbin ~/.stack
sudo mkdir -p /opt/bun-1.4.4 && curl -fsSL https://bun.sh/install | sudo BUN_INSTALL=/opt/bun-1.4.4 bash -s bun-v1.4.4 && /opt/bun-1.4.4/bin/bun --version
curl -fsSL -o /tmp/cvc5.zip https://github.com/cvc5/cvc5/releases/download/cvc5-{CVC5}/cvc5-Linux-x86_64-static.zip
sudo unzip -q -o /tmp/cvc5.zip -d /opt && sudo ln -sf $(find /opt -path '*cvc5-Linux-x86_64-static/bin/cvc5') /usr/local/bin/cvc5 && cvc5 --version | head -1
curl -fsSL -o /tmp/vampire.zip https://github.com/vprover/vampire/releases/download/{VAMPIRE}/vampire-Linux-X64.zip
sudo mkdir -p /opt/vampire && sudo unzip -q -o /tmp/vampire.zip -d /opt/vampire && sudo ln -sf $(find /opt/vampire -type f -name 'vampire*' | head -1) /usr/local/bin/vampire
sudo chmod +x /usr/local/bin/vampire && vampire --version
mkdir -p /opt/gdpw/tip/bench && curl -fsSL https://codeload.github.com/tip-org/benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /opt/gdpw/tip/bench --strip-components 1
sudo rmdir /bench && sudo ln -s /opt/gdpw/tip/bench /bench
python3 - <<'PY'
{CONVERT}
PY
python3 - <<'PY'
{WILD}
PY
sudo rm /bench && sudo mkdir /bench
"""
# proveData peaks at 4 to 5.5 GB on some tasks (list_PairEvens, sort_MSortBUCount, lemma_07, measured alone): over a
# Modal container's 4 GB request, which Modal doesn't hold it to. Two to a VM's 8 GB, two such tasks at once ran out of
# memory, so each call takes a whole default VM (weight 2).
BOAT = {"mounts": {"/bench": "/opt/gdpw/tip/bench"}, "path": ["/opt/bun-1.4.4/bin"], "weight": 2}

# cvc5: `--quant-ind` (induction by skolemisation with strengthening, Reynolds & Kuncak, VMCAI 2015); `cvc5cg` adds their
# subgoal generation (`--conjecture-gen`, three conjectures a round) with full saturation of quantifiers, the
# configuration the TIP paper ran CVC4 in (Claessen, Johansson, Rosén, Smallbone, CICM 2015) save `--quant-cf`, gone.
CVC5_FLAGS = {
    "cvc5": ["--lang", "smt2", "--quant-ind"],
    "cvc5cg": ["--lang", "smt2", "--quant-ind", "--conjecture-gen", "--conjecture-gen-per-round=3", "--full-saturate-quant"],
}
# Vampire: its induction schedule (structural and integer induction with generalisation, the strategies tuned on TIP and
# SMT-LIB's UFDT/UFDTLIA), as a portfolio over the container's 2 cores.
VAMPIRE_FLAGS = ["--input_syntax", "smtlib2", "--mode", "portfolio", "--schedule", "induction", "--cores", "2"]


def command(tool: str, task: str, limit: int, extra: list[str] = []) -> list[str]:
    if tool == "gdptr":
        return ["bun", "compare/tip/solve.ts", f"/bench/benchmarks/{task}", "--translate-only"]
    if tool == "gdp":
        # proveData's own budget 3 s before the limit, so it says unknown rather than being killed
        return ["bun", "compare/tip/solve.ts", f"/bench/benchmarks/{task}", "--ms", str((limit - 3) * 1000), *extra]
    if tool in CVC5_FLAGS:
        return ["cvc5", *CVC5_FLAGS[tool], f"/smt/{task}"]
    if tool == "vampire":
        return ["vampire", *VAMPIRE_FLAGS, "--time_limit", str(limit), f"/vamp/{task}"]
    raise ValueError(tool)


def answer_of(tool: str, code: int, out: str) -> str:
    lines = [l.strip() for l in out.splitlines() if l.strip()]
    if tool in CVC5_FLAGS:
        # the goal negated: unsat is the goal proven, sat a model of its negation
        word = next((l for l in lines if l in ("sat", "unsat", "unknown")), None)
        return {"unsat": "proven", "sat": "refuted", "unknown": "unknown"}.get(word or "", "timeout" if code == 124 else "error")
    if tool == "vampire":
        import re
        if any(re.search(r"SZS status (Theorem|Unsatisfiable)\b|Termination reason: Refutation$", l) for l in lines):
            return "proven"
        if any(re.search(r"SZS status (CounterSatisfiable|Satisfiable)\b|Termination reason: Satisfiable$", l) for l in lines):
            return "refuted"
        if any("SZS status" in l for l in lines):
            return "unknown"
        return "timeout" if code == 124 else "unknown" if code in (0, 1) else "error"
    raise ValueError(tool)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=3600)
def shard(tool: str, tasks: list[str], limit: int, extra: dict = {}) -> list[dict]:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    rows = []
    for task in tasks:
        t0 = time.time()
        if tool != "gdp" and not pathlib.Path(f"/{'vamp' if tool == 'vampire' else 'smt'}/{task}").exists():
            rows.append({"tool": tool, "task": task, "answer": "error", "seconds": 0, "err": "tip's translation failed"})
            continue
        try:
            # (`--trace` among the gdp args: proveData's trace, DATA_TRACE, kept in the row, its last 400 KB; `--env=K=V`
            # sets K, DATA_NODE=<regex> say: diagnostics)
            args = extra.get(task, []) + extra.get("*", [])
            trace = "--trace" in args
            envs = dict(a[len("--env="):].split("=", 1) for a in args if a.startswith("--env="))
            args = [a for a in args if a != "--trace" and not a.startswith("--env=")]
            p = subprocess.run(["timeout", "-k", "5", str(limit), *command(tool, task, limit, args)], cwd=work, capture_output=True, text=True, timeout=limit + 30,
                               env={**os.environ, **envs, **({"DATA_TRACE": "1"} if trace else {})} if trace or envs else None)
            code, out, err = p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired:
            code, out, err = 124, "", "killed"
        secs = round(time.time() - t0, 2)
        if tool in ("gdp", "gdptr"):
            stages = []
            for l in out.splitlines():
                try:
                    stages.append(json.loads(l))
                except json.JSONDecodeError:
                    pass
            last = stages[-1] if stages and stages[-1].get("stage") == "answer" else {}
            answer = last.get("answer", "timeout" if code == 124 else "error")
            for s in stages:
                s.pop("task", None)
            row = {"tool": tool, "task": task, "answer": answer, "seconds": secs, "stages": stages, **({"trace": err[-400_000:]} if trace else {})}
        else:
            answer = answer_of(tool, code, out)
            row = {"tool": tool, "task": task, "answer": answer, "seconds": secs}
        if answer == "error":
            row["err"] = (out[-500:] + " || " + "\n".join(l for l in err.splitlines() if "set-logic" not in l and "stricter logic" not in l and "cvc5 will make" not in l)[-500:])
        rows.append(row)
    return rows


@app.function(scaledown_window=2, timeout=600)
def tasks(sets: list[str]) -> dict:
    root = pathlib.Path("/bench/benchmarks")
    out = [str(f.relative_to(root)) for d in sets for f in sorted((root / d).glob("*.smt2"))]
    return {"tasks": out, "convert_errors": json.loads(pathlib.Path("/smt/convert-errors.json").read_text())}


@app.function(scaledown_window=2, timeout=900, cpu=2.0)
def probe(cmds: list[str]) -> str:
    import subprocess

    def sh(c: str) -> str:
        p = subprocess.run(c, shell=True, capture_output=True, text=True)
        return f"$ {c}\n{p.stdout[-3000:]}{p.stderr[-1500:]}"
    return "\n".join(sh(c) for c in cmds or [
        "cvc5 --version | head -2", "vampire --version", "bun --version", "cat /smt/convert-errors.json | head -40",
        "find /smt -name '*.smt2' | wc -l; find /vamp -name '*.smt2' | wc -l",
        "cat /smt/isaplanner/prop_01.smt2", "cat /vamp/isaplanner/prop_01.smt2",
        "timeout 20 cvc5 --lang smt2 --quant-ind /smt/isaplanner/prop_01.smt2",
        "timeout 20 cvc5 --lang smt2 --quant-ind --conjecture-gen --conjecture-gen-per-round=3 --full-saturate-quant /smt/isaplanner/prop_01.smt2",
        "vampire --show_options on 2>&1 | grep -i -A3 'schedule\\b' | head -30",
        "timeout 25 vampire --input_syntax smtlib2 --mode portfolio --schedule induction --cores 2 --time_limit 20 /vamp/isaplanner/prop_01.smt2 | grep -i 'szs\\|termination\\|strategy\\|schedule' | head",
        "vampire --show_options on 2>&1 | grep -A12 -- '^--schedule ' | head -14",
    ])


@app.local_entrypoint()
def main(out: str = "", tools: str = "gdp,cvc5,cvc5cg,vampire", limit: int = 60, sets: str = "isaplanner,prod,tip2015,grammars", only: str = "", sample: int = 0, per: int = 1, probe_only: bool = False, probe_cmd: str = "", gdp_args: str = "", lemmas: str = ""):
    import sys
    sys.path.insert(0, str(GDP / "modal"))
    import fanout
    run(fanout.ModalEx(app), out, tools, limit, sets, only, sample, per, probe_only, probe_cmd, gdp_args, lemmas)


def run(ex, out: str = "", tools: str = "gdp,cvc5,cvc5cg,vampire", limit: int = 60, sets: str = "isaplanner,prod,tip2015,grammars", only: str = "", sample: int = 0, per: int = 1, probe_only: bool = False, probe_cmd: str = "", gdp_args: str = "", lemmas: str = ""):
    t0 = time.time()
    try:
        if probe_only:
            print(ex.remote(probe, [c for c in probe_cmd.split(";;") if c.strip()]))
            return
        outdir = pathlib.Path(out)
        outdir.mkdir(parents=True, exist_ok=True)
        got = ex.remote(tasks, sets.split(","))
        (outdir / "tasks.json").write_text(json.dumps({"gdp_args": gdp_args, "lemmas": lemmas, "only": only, "bench": BENCH_COMMIT, "tools": TOOLS_COMMIT, "cvc5": CVC5, "vampire": VAMPIRE, "limit": limit,
                                                       "flags": {**CVC5_FLAGS, "vampire": VAMPIRE_FLAGS}, **got}, indent=1))
        # diagnostics: `--gdp-args` added to every gdp-wired task's command; `--lemmas <json>` ({task: [TIP formula, ..]})
        # gives those tasks the lemmas (solve.ts --lemma) and runs those tasks alone
        extra: dict = {"*": gdp_args.split()} if gdp_args else {}
        if lemmas:
            given = json.loads(pathlib.Path(lemmas).read_text())
            for t, ls in given.items():
                extra[t] = [a for l in ls for a in ("--lemma", l)]
            only = "|".join(given)
        chosen = [t for t in got["tasks"] if any(o == t if lemmas else o in t for o in only.split("|"))]
        if sample:
            chosen = chosen[::max(1, len(chosen) // sample)][:sample]
        shards = [(tool, chosen[i:i + per], limit, extra) for tool in tools.split(",") for i in range(0, len(chosen), per)]
        print(f"{len(chosen)} tasks, {len(shards)} containers", flush=True)
        n = 0
        with (outdir / "results.jsonl").open("w") as f:
            for rows in ex.starmap(shard, shards):
                if isinstance(rows, BaseException):
                    rows = [{"tool": "?", "task": "?", "answer": "error", "err": repr(rows)[:400]}]
                for r in rows:
                    f.write(json.dumps(r) + "\n")
                n += 1
                if n % 100 == 0:
                    print(f"{n}/{len(shards)}, {round(time.time() - t0)} s", flush=True)
    finally:
        ex.close()
    print(f"done in {round(time.time() - t0, 1)} s wall")


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(GDP / "modal"))
    import fanout
    fanout.cli(run, __file__, __doc__)
