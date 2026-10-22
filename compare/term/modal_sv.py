"""SV-COMP's termination tasks of the ControlFlow-Termination set (sv-benchmarks, c/termination-crafted, -crafted-lit,
-numeric, -restricted-15, -nla: each task with termination.prp and its expected verdict) on Modal: gdp-wired on its
translation (c2ari.py, then solve.ts) beside Ultimate Automizer on the C program, and LoAT and KoAT2 on gdp-wired's
translation; each task in its own container (2 vCPU, 4 GB), each tool under the same wall-clock limit (the
translation inside it), all at once.

    modal run compare/term/modal_sv.py --out runs/modal/term/<name> [--tools gdp,gdp-scc,uautomizer,loat-abmc,koat2]
                                       [--limit 60] [--only <substring>|<substring>]

<out>/results.jsonl has one row per tool and task: the answer (terminates, nonterminating, unknown, unsupported,
timeout, error), the seconds, the expected verdict and, for gdp-wired, the translation's line and the stages.
"""
import json
import os
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
SV_COMMIT = "c5cc603f325550a65b94a7d9dbfcf7896ad28b91"
DIRS = ["termination-crafted", "termination-crafted-lit", "termination-numeric", "termination-restricted-15", "termination-nla"]
UA = "v0.3.1"
LOAT = "v0.9.10"
KOAT = "v2.7.0"

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "zstd", "coreutils", "openjdk-21-jre-headless")
    .pip_install("pycparser==3.0")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        f"curl -fsSL -o /tmp/ua.zip https://github.com/ultimate-pa/ultimate/releases/download/{UA}/UltimateAutomizer-linux.zip && unzip -q /tmp/ua.zip -d /opt && rm /tmp/ua.zip",
        f"curl -fsSL -o /usr/local/bin/loat https://github.com/LoAT-developers/LoAT/releases/download/{LOAT}/loat-static && chmod +x /usr/local/bin/loat",
        f"curl -fsSL https://github.com/aprove-developers/KoAT2-Releases/releases/download/{KOAT}/koat2_static.zst | zstd -d > /usr/local/bin/koat2 && chmod +x /usr/local/bin/koat2",
        "mkdir -p /sv && cd /sv && for d in " + " ".join([*DIRS, "properties"]) + f"; do curl -fsSL 'https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/archive/{SV_COMMIT}/sv-benchmarks-{SV_COMMIT}.tar.gz?path=c/'$d | tar xz --strip-components 1; done && ls /sv/c",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "modal/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "docs/**", "static/**", "lean-kernel/.lake/**"])
)
app = modal.App("gdp-wired-term-sv", image=image)

KOAT_SH = "sed -e 's/\\^/_hat_/g' -e \"s/'/_q_/g\" -e 's/|//g' \"$1\" > /tmp/k.ari && koat2 ari-to-koat /tmp/k.ari --output-file /tmp/t.koat > /dev/null && koat2 analyse --termination -i /tmp/t.koat"


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=3600)
def shard(tool: str, t: dict, limit: int) -> dict:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    c = f"/sv/c/{t['c']}"
    t0 = time.time()
    row = {"tool": tool, "task": t["task"], "expected": t["expected"]}

    def run(cmd, secs):
        try:
            p = subprocess.run(["timeout", "-k", "5", str(max(1, int(secs))), *cmd], cwd=work, capture_output=True, text=True, timeout=secs + 30)
            return p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired:
            return 124, "", "killed"

    if tool == "uautomizer":
        code, out, err = run(["python3", "/opt/UAutomizer-linux/Ultimate.py", "--spec", "/sv/c/properties/termination.prp", "--architecture", t["arch"], "--file", c], limit)
        lines = out.splitlines()
        word = next((lines[i + 1].strip() for i, l in enumerate(lines) if l.strip() == "Result:" and i + 1 < len(lines)), None)
        answer = {"TRUE": "terminates", "FALSE(TERM)": "nonterminating", "UNKNOWN": "unknown"}.get(word or "", None)
        if answer is None and word and word.startswith("FALSE"):
            answer = "nonterminating"
        answer = answer or ("timeout" if code == 124 else "error")
        row.update(answer=answer, seconds=round(time.time() - t0, 2))
        if answer == "error":
            row["err"] = (err or out)[-600:]
        return row
    # the others read gdp-wired's translation
    code, ari, err = run(["python3", "compare/term/c2ari.py", c], limit)
    info = json.loads(err.strip().splitlines()[-1]) if err.strip() else {}
    row["translation"] = info
    if code != 0:
        row.update(answer="unsupported", seconds=round(time.time() - t0, 2), why=info.get("refused", err[-300:]))
        return row
    pathlib.Path("/tmp/t.ari").write_text(ari)
    left = limit - (time.time() - t0)
    if tool in ("gdp", "gdp-scc"):
        code, out, err = run(["bun", "compare/term/solve.ts", "/tmp/t.ari", "--limit", str(int(left)), *(["--scc"] if tool == "gdp-scc" else [])], left)
        stages = []
        for l in out.splitlines():
            try:
                stages.append(json.loads(l))
            except json.JSONDecodeError:
                pass
        answer = (stages[-1] if stages else {}).get("answer", "timeout" if code == 124 else "error")
        row.update(answer=answer, stages=stages)
    elif tool in ("loat", "loat-abmc"):
        code, out, err = run(["loat", "--mode", "termination", *(["--engine", "abmc"] if tool == "loat-abmc" else []), "/tmp/t.ari"], left)
        w = next((l.strip() for l in out.splitlines() if l.strip() in ("YES", "NO", "MAYBE")), None)
        answer = {"YES": "terminates", "NO": "nonterminating", "MAYBE": "unknown"}.get(w or "", "timeout" if code == 124 else "error")
        row["answer"] = answer
    elif tool == "koat2":
        code, out, err = run(["bash", "-c", KOAT_SH, "koat", "/tmp/t.ari"], left)
        w = next((l.strip() for l in out.splitlines() if l.strip() in ("Finite", "Infinite")), None)
        row["answer"] = {"Finite": "terminates", "Infinite": "unknown"}.get(w or "", "timeout" if code == 124 else "error")
    else:
        raise ValueError(tool)
    row["seconds"] = round(time.time() - t0, 2)
    if row["answer"] == "error":
        e = err or out
        row["err"] = e if len(e) <= 900 else e[:300] + " ... " + e[-600:]
    return row


@app.function(scaledown_window=2, timeout=600)
def tasks() -> list[dict]:
    import re
    out = []
    for d in DIRS:
        for y in sorted(pathlib.Path(f"/sv/c/{d}").glob("*.yml")):
            text = y.read_text()
            m = re.search(r"termination\.prp\s*\n\s*expected_verdict:\s*(\w+)", text)
            if not m:
                continue
            c = re.search(r"input_files:\s*'?([^'\n]+)'?", text).group(1).strip()
            dm = re.search(r"data_model:\s*(\w+)", text)
            out.append({"task": f"{d}/{y.name}", "c": f"{d}/{c}", "expected": "terminates" if m.group(1) == "true" else "nonterminating",
                        "arch": "32bit" if dm and dm.group(1) == "ILP32" else "64bit"})
    return out


@app.function(scaledown_window=2, timeout=600)
def versions() -> dict:
    import subprocess
    run = lambda c: subprocess.run(["bash", "-c", c], capture_output=True, text=True).stdout
    return {"uautomizer": run("cd /opt/UAutomizer-linux && python3 Ultimate.py --ultversion 2>&1 | tail -3"), "java": run("java -version 2>&1 | head -1"),
            "koat2": run("koat2 --version 2>&1 | grep -i version"), "bun": run("bun --version"), "pycparser": run("python3 -c 'import pycparser; print(pycparser.__version__)'")}


@app.local_entrypoint()
def main(out: str, tools: str = "gdp,gdp-scc,uautomizer,loat-abmc,koat2", limit: int = 60, only: str = ""):
    live = GDP / "modal" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    try:
        all_tasks = tasks.remote()
        (outdir / "tasks.json").write_text(json.dumps(all_tasks, indent=1))
        (outdir / "versions.json").write_text(json.dumps({**versions.remote(), "sv_benchmarks": SV_COMMIT, "dirs": DIRS, "uautomizer_release": UA, "loat_release": LOAT, "koat2_release": KOAT, "limit": limit, "tools": tools}, indent=1))
        chosen = [t for t in all_tasks if any(o in t["task"] for o in only.split("|"))]
        jobs = [(tool, t, limit) for tool in tools.split(",") for t in chosen]
        print(f"{len(chosen)} tasks, {len(jobs)} containers", flush=True)
        with (outdir / "results.jsonl").open("w") as f:
            for r in shard.starmap(jobs, order_outputs=False, return_exceptions=True):
                if isinstance(r, BaseException):
                    r = {"tool": "?", "task": "?", "answer": "error", "err": repr(r)[:400]}
                f.write(json.dumps(r) + "\n")
                f.flush()
    finally:
        ticket.unlink(missing_ok=True)
    print(f"done in {round(time.time() - t0, 1)} s wall")
