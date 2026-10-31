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

try:
    import modal
except ImportError:  # plain python3, --backend boat: the runner's functions run on boat VMs (supercomputer/fanout.py)
    import sys
    sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent.parent.parent / "supercomputer"))
    from agent import modal_stub
    modal = modal_stub()

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
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "supercomputer/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "docs/**", "static/**", "lean-kernel/.lake/**"])
)
app = modal.App("gdp-wired-term-sv", image=image)

# The same image on a boat VM, a layer of the pool's snapshot (supercomputer/boat.py). Ultimate writes into its own directory
# (as root, a container each, on Modal): each call gets a private overlay of it (BOAT).
BOAT_SETUP = f"""
sudo apt-get install -y -q openjdk-21-jre-headless
sudo pip3 install -q --break-system-packages pycparser==3.0
curl -fsSL -o /tmp/ua.zip https://github.com/ultimate-pa/ultimate/releases/download/{UA}/UltimateAutomizer-linux.zip && sudo unzip -q -o /tmp/ua.zip -d /opt && rm /tmp/ua.zip
sudo chown -R "$(id -un)" /opt/UAutomizer-linux
curl -fsSL -o /tmp/loat https://github.com/LoAT-developers/LoAT/releases/download/{LOAT}/loat-static && sudo install -m 755 /tmp/loat /usr/local/bin/loat
curl -fsSL https://github.com/aprove-developers/KoAT2-Releases/releases/download/{KOAT}/koat2_static.zst | zstd -d > /tmp/koat2 && sudo install -m 755 /tmp/koat2 /usr/local/bin/koat2
mkdir -p /sv && cd /sv && for d in {" ".join([*DIRS, "properties"])}; do curl -fsSL "https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/archive/{SV_COMMIT}/sv-benchmarks-{SV_COMMIT}.tar.gz?path=c/$d" | tar xz --strip-components 1; done && ls /sv/c
"""
BOAT = {"overlays": ["/opt/UAutomizer-linux"]}

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
    # the others read gdp-wired's translation (the task's data model, and whether it declares no signed overflow); a
    # recursive program has two, each exact for one answer: --for terminates, --for nonterminating
    yml = f"/sv/c/{t['task']}"
    code, ari, err = run(["python3", "compare/term/c2ari.py", c, "--yml", yml, "--for", "terminates"], limit)
    info = json.loads(err.strip().splitlines()[-1]) if err.strip() else {}
    row["translation"] = info
    if code != 0:
        row.update(answer="unsupported", seconds=round(time.time() - t0, 2), why=info.get("refused", err[-300:]))
        return row
    pathlib.Path("/tmp/t.ari").write_text(ari)
    split = info.get("split", False)
    if split:
        code, ari2, err2 = run(["python3", "compare/term/c2ari.py", c, "--yml", yml, "--for", "nonterminating"], limit - (time.time() - t0))
        row["translation_nt"] = json.loads(err2.strip().splitlines()[-1]) if err2.strip() else {}
        if code != 0:
            row.update(answer="unsupported", seconds=round(time.time() - t0, 2), why=row["translation_nt"].get("refused", err2[-300:]))
            return row
        pathlib.Path("/tmp/t-nt.ari").write_text(ari2)
    # signed overflow checked (the task declares none impossible): beside it, the translation that checks none, read
    # only for "terminates" (gdp-wired's tools)
    unchecked = tool in ("gdp", "gdp-scc") and not split and "overflow checked" in info.get("features", [])
    if unchecked:
        code, ari3, err3 = run(["python3", "compare/term/c2ari.py", c, "--yml", yml, "--unchecked"], limit - (time.time() - t0))
        row["translation_unchecked"] = json.loads(err3.strip().splitlines()[-1]) if err3.strip() else {}
        unchecked = code == 0
        if unchecked:
            pathlib.Path("/tmp/t-u.ari").write_text(ari3)
    left = limit - (time.time() - t0)

    def stages_of(out):
        st = []
        for l in out.splitlines():
            try:
                st.append(json.loads(l))
            except json.JSONDecodeError:
                pass
        return st

    # the last answer printed: a proof's answer comes once the kernel has checked its trees again, before its certificate
    # is made, so a run stopped while making it keeps the answer (cert "not made")
    def last_answer(st):
        return next((x for x in reversed(st) if "answer" in x), {}).get("answer")
    if tool in ("gdp", "gdp-scc"):
        cmd = lambda f, *more: ["timeout", "-k", "5", str(max(1, int(left))), "bun", "compare/term/solve.ts", f, "--limit", str(int(left)), *(["--scc"] if tool == "gdp-scc" else []), *more]
        if not split and not unchecked:
            code, out, err = run(cmd("/tmp/t.ari")[4:], left)
            stages = stages_of(out)
            answer = last_answer(stages) or ("timeout" if code == 124 else "error")
            row.update(answer=answer, stages=stages)
        else:
            # the two side by side (a vCPU each): a recursive program's two translations, each searching only for its
            # answer; or the checked translation (both answers) and the unchecked one (terminates)
            pair = (("/tmp/t.ari", ["--want", "terminates"]), ("/tmp/t-nt.ari", ["--want", "nonterminating"])) if split else \
                (("/tmp/t-u.ari", ["--want", "terminates"]), ("/tmp/t.ari", []))
            ps = [subprocess.Popen(cmd(f, *w), cwd=work, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True) for f, w in pair]
            outs = []
            for q in ps:
                try:
                    o, e = q.communicate(timeout=left + 30)
                except subprocess.TimeoutExpired:
                    q.kill()
                    o, e = q.communicate()
                outs.append((q.returncode, o, e))
            st_t, st_n = stages_of(outs[0][1]), stages_of(outs[1][1])
            a_t = last_answer(st_t)
            a_n = last_answer(st_n)
            if a_t == "terminates" and a_n == "nonterminating":
                answer = "error"
                row["err"] = "both answers"
            elif not split and a_n in ("terminates", "nonterminating"):
                answer = a_n  # the checked translation's own answer
            elif a_t == "terminates" or a_n == "nonterminating":
                answer = a_t if a_t == "terminates" else a_n
            elif a_t is None and a_n is None:
                answer = "timeout" if outs[0][0] == 124 else "error"
            else:
                answer = "unknown"
            err = outs[0][2] + outs[1][2]
            row.update(answer=answer, **({"stages": st_t, "stages_nt": st_n} if split else {"stages": st_n, "stages_unchecked": st_t}))
    elif tool in ("loat", "loat-abmc"):
        code, out, err = run(["loat", "--mode", "termination", *(["--engine", "abmc"] if tool == "loat-abmc" else []), "/tmp/t.ari"], left)
        w = next((l.strip() for l in out.splitlines() if l.strip() in ("YES", "NO", "MAYBE")), None)
        answer = {"YES": "terminates", "NO": "nonterminating", "MAYBE": "unknown"}.get(w or "", "timeout" if code == 124 else "error")
        if split and answer == "nonterminating":
            answer = "unknown"  # read on the translation exact only for "terminates"
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
    import sys
    sys.path.insert(0, str(GDP / "supercomputer"))
    import fanout
    run(fanout.ModalEx(app), out, tools, limit, only)


def run(ex, out: str, tools: str = "gdp,gdp-scc,uautomizer,loat-abmc,koat2", limit: int = 60, only: str = ""):
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    try:
        all_tasks = ex.remote(tasks)
        (outdir / "tasks.json").write_text(json.dumps(all_tasks, indent=1))
        (outdir / "versions.json").write_text(json.dumps({**ex.remote(versions), "sv_benchmarks": SV_COMMIT, "dirs": DIRS, "uautomizer_release": UA, "loat_release": LOAT, "koat2_release": KOAT, "limit": limit, "tools": tools}, indent=1))
        chosen = [t for t in all_tasks if any(o in t["task"] for o in only.split("|"))]
        jobs = [(tool, t, limit) for tool in tools.split(",") for t in chosen]
        print(f"{len(chosen)} tasks, {len(jobs)} containers", flush=True)
        with (outdir / "results.jsonl").open("w") as f:
            for r in ex.starmap(shard, jobs):
                if isinstance(r, BaseException):
                    r = {"tool": "?", "task": "?", "answer": "error", "err": repr(r)[:400]}
                f.write(json.dumps(r) + "\n")
                f.flush()
    finally:
        ex.close()
    print(f"done in {round(time.time() - t0, 1)} s wall")


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(GDP / "supercomputer"))
    import fanout
    fanout.cli(run, __file__, __doc__)
