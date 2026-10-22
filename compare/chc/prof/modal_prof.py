"""Profiles of compare/chc/prof/prove.ts on Modal: `modal run compare/chc/prof/modal_prof.py --out <dir> --tasks a,b,c [--prof]`.
Each task in its own container (the image of ../modal_chc.py); stdout, stderr (PROVE_TRACE) and, with --prof, the top
self-time functions of bun's CPU profile land in <dir>/<task>.log."""
import json
import os
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent.parent
BENCH_COMMIT = "b4fa7a708e5863bbcdb5de50d692ead3a67cbedc"
KEEP = r"""
import pathlib, re, shutil
root = pathlib.Path('/bench')
keep = set()
for y in (root / 'LIA-Lin.set').read_text().split():
    y = root / y
    keep.add(y)
    m = re.search(r'^input_files:\s*(\S+)', y.read_text(), re.M)
    keep.add(y.parent / m.group(1))
for p in sorted(root.rglob('*'), reverse=True):
    if p.is_file() and p not in keep and p.name != 'LIA-Lin.set':
        p.unlink()
    elif p.is_dir() and not any(p.iterdir()):
        p.rmdir()
"""

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "bzip2", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
        " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3 && z3 --version",
        "curl -fsSL https://github.com/usi-verification-and-security/golem/releases/download/v0.9.0/golem-x64-linux.tar.bz2"
        " | tar xj -C /opt && find /opt -name golem -type f -exec ln -s {} /usr/local/bin/golem \\; && golem --version",
        "curl -fsSL https://github.com/uuverifiers/eldarica/releases/download/v2.3/eldarica-x86-linux-static.gz | gunzip > /usr/local/bin/eld"
        " && chmod +x /usr/local/bin/eld && eld -h | head -3",
        f"mkdir /bench && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/{BENCH_COMMIT} | tar xz -C /bench --strip-components 1",
    )
    .run_commands(f"python3 - <<'EOF'\n{KEEP}\nEOF", "du -sh /bench")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "modal/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**"])
)
app = modal.App("gdp-wired-chc-prof", image=image)

TOP = r"""
import json, sys, collections
p = json.load(open(sys.argv[1]))
nodes = {n['id']: n for n in p['nodes']}
self_t = collections.Counter()
dt = p.get('timeDeltas', [])
for sid, d in zip(p['samples'], dt):
    cf = nodes[sid]['callFrame']
    self_t[(cf['functionName'] or '(anon)', cf['url'].split('/')[-1], cf['lineNumber'] + 1)] += d
tot = sum(self_t.values()) or 1
for (fn, url, line), t in self_t.most_common(30):
    print(f"{t/1000:9.0f} ms {100*t/tot:5.1f}%  {fn}  {url}:{line}")
"""


@app.function(scaledown_window=2, cpu=2.0, memory=8192, timeout=1800)
def one(task: str, prof: bool, env: dict) -> str:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    cmd = ["bun", *(["--cpu-prof", "--cpu-prof-dir=/tmp/prof"] if prof else []), "compare/chc/prof/prove.ts", f"/bench/{task}"]
    t0 = time.time()
    p = subprocess.run(["timeout", "600", *cmd], cwd=work, capture_output=True, text=True, env={**os.environ, **env})
    out = f"exit {p.returncode} in {round(time.time() - t0, 1)} s\n{p.stdout}\n--- stderr ---\n{p.stderr[-60000:]}"
    if prof:
        for f in pathlib.Path("/tmp/prof").glob("*.cpuprofile"):
            q = subprocess.run(["python3", "-c", TOP, str(f)], capture_output=True, text=True)
            out += "\n--- profile ---\n" + q.stdout + q.stderr
    return out


@app.local_entrypoint()
def main(out: str, tasks: str, prof: bool = False, trace: bool = False):
    live = GDP / "modal" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    env = {"PROVE_TRACE": "1"} if trace else {}
    calls = []
    try:
        names = tasks.split(",")
        calls = [one.spawn(t, prof, env) for t in names]
        for t, c in zip(names, calls):
            text = c.get()
            (outdir / (pathlib.Path(t).stem + ".log")).write_text(text)
            print(t, text.splitlines()[0], flush=True)
    finally:
        for c in calls:
            try:
                c.cancel()
            except Exception:
                pass
        ticket.unlink(missing_ok=True)
