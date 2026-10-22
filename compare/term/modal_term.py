"""TermComp's integer transition systems (TPDB-ARI's Integer_Transition_Systems) on Modal: gdp-wired (solve.ts) beside
LoAT and KoAT2, each task in its own container (2 vCPU, 4 GB), each tool under the same wall-clock limit, all at once.

    modal run compare/term/modal_term.py --out runs/modal/term/<name> [--tools gdp,loat,loat-abmc,koat2] [--limit 60]
                                         [--sample 0] [--only <substring>|<substring>] [--tasks-file <names, one a line>]
                                         [--env NAME=value,...]

The benchmarks are TermCOMP/TPDB-ARI at a pinned commit, fetched into the image. <out>/results.jsonl has one row per
tool and task: the answer (terminates, nonterminating, unknown, unsupported, timeout, error), the seconds and, for
gdp-wired, the stages it printed. The app id and client pid are registered in modal/.live/ (modal/reap.sh stops an
orphan); the app, and every call in it, stops when this entrypoint exits.
"""
import json
import os
import pathlib
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parent.parent
ARI_COMMIT = "183f29db5ec7702215c6aabe12732bf3e836fced"
LOAT = "v0.9.10"
KOAT = "v2.7.0"

image = (
    modal.Image.from_registry("ubuntu:24.04", add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "zstd", "coreutils")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        f"curl -fsSL -o /usr/local/bin/loat https://github.com/LoAT-developers/LoAT/releases/download/{LOAT}/loat-static && chmod +x /usr/local/bin/loat",
        f"curl -fsSL https://github.com/aprove-developers/KoAT2-Releases/releases/download/{KOAT}/koat2_static.zst | zstd -d > /usr/local/bin/koat2 && chmod +x /usr/local/bin/koat2",
        f"mkdir /bench && curl -fsSL https://codeload.github.com/TermCOMP/TPDB-ARI/tar.gz/{ARI_COMMIT} | tar xz -C /bench --strip-components 1 TPDB-ARI-{ARI_COMMIT}/Integer_Transition_Systems",
        "find /bench -name '*.ari' | wc -l",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=["node_modules", "**/*.olean", "**/*.ilean", "**/node_modules/**", "**/runs/**", "runs/**", "modal/**", "private/**",
                                              "vendor/**", "compare/**/*.js", "compare/**/out/**", "docs/**", "static/**", "lean-kernel/.lake/**"])
)
app = modal.App("gdp-wired-term", image=image)

# KoAT2 reads its own format: the task through `koat2 ari-to-koat` first, with `^` in names (T2's x^0) and the quoted
# symbols of the AProVE tasks (|f274_0_power_LE'|) renamed (KoAT's parsers refuse them; a renaming, nothing else).
KOAT_SH = "sed -e 's/\\^/_hat_/g' -e \"s/'/_q_/g\" -e 's/|//g' \"$1\" > /tmp/t.ari && koat2 ari-to-koat /tmp/t.ari --output-file /tmp/t.koat > /dev/null && koat2 analyse --termination -i /tmp/t.koat"


def command(tool: str, task: str, limit: int) -> list[str]:
    if tool == "gdp":
        return ["bun", "compare/term/solve.ts", task, "--limit", str(limit)]
    if tool == "gdp-scc":
        return ["bun", "compare/term/solve.ts", task, "--limit", str(limit), "--scc"]
    if tool == "loat":
        return ["loat", "--mode", "termination", task]
    if tool == "loat-abmc":
        return ["loat", "--mode", "termination", "--engine", "abmc", task]
    if tool == "koat2":
        return ["bash", "-c", KOAT_SH, "koat", task]
    # diagnostics: the same runs with the proof printed (kept in the row's `out`), to read which technique answered
    if tool == "koat2-proof":
        return ["bash", "-c", KOAT_SH + " --show-proof", "koat", task]
    if tool == "loat-proof":
        return ["loat", "--mode", "termination", "--proof", task]
    if tool == "loat-abmc-proof":
        return ["loat", "--mode", "termination", "--engine", "abmc", "--proof", task]
    raise ValueError(tool)


def answer_of(tool: str, lines: list[str]) -> str | None:
    tool = tool.removesuffix("-proof")
    if tool.startswith("loat"):
        w = next((l.strip() for l in lines if l.strip() in ("YES", "NO", "MAYBE")), None)
        return {"YES": "terminates", "NO": "nonterminating", "MAYBE": "unknown", None: None}[w]
    if tool == "koat2":
        # KoAT2 --termination: "Finite" where it proves every run ends, "Infinite" where it doesn't (no claim)
        w = next((l.strip() for l in lines if l.strip() in ("Finite", "Infinite")), None)
        return {"Finite": "terminates", "Infinite": "unknown", None: None}[w]
    raise ValueError(tool)


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=3600)
def shard(tool: str, tasks: list[dict], limit: int, env: str = "") -> list[dict]:
    import shutil
    import subprocess

    work = pathlib.Path("/work/gdp-wired")
    if not work.exists():
        shutil.copytree("/src/gdp-wired", work)
    rows = []
    for t in tasks:
        path = f"/bench/{t['task']}"
        t0 = time.time()
        try:
            extra = dict(kv.split("=", 1) for kv in env.split(",") if kv)
            p = subprocess.run(["timeout", "-k", "5", str(limit), *command(tool, path, limit)], cwd=work, capture_output=True, text=True, timeout=limit + 30, env={**os.environ, **extra})
            code, out, err = p.returncode, p.stdout, p.stderr
        except subprocess.TimeoutExpired:
            code, out, err = 124, "", "killed"
        secs = round(time.time() - t0, 2)
        lines = [l for l in out.splitlines() if l.strip()]
        if tool.startswith("gdp"):
            stages = []
            for l in lines:
                try:
                    stages.append(json.loads(l))
                except json.JSONDecodeError:
                    pass
            last = stages[-1] if stages else {}
            answer = last.get("answer", "timeout" if code == 124 else "error")
            row = {"tool": tool, "task": t["task"], "answer": answer, "seconds": secs, "stages": stages}
        else:
            answer = answer_of(tool, lines) or ("timeout" if code == 124 else "error")
            row = {"tool": tool, "task": t["task"], "answer": answer, "seconds": secs}
            if tool.endswith("-proof"):
                row["out"] = out[:30000]
        if answer == "error":
            row["err"] = (err or out)[-600:]
            row["code"] = code
        rows.append(row)
    return rows


@app.function(scaledown_window=2, timeout=600)
def tasks() -> list[dict]:
    root = pathlib.Path("/bench")
    return [{"task": str(p.relative_to(root)), "bytes": p.stat().st_size} for p in sorted(root.rglob("*.ari"))]


@app.function(scaledown_window=2, timeout=600)
def versions() -> dict:
    import subprocess
    run = lambda c: subprocess.run(["bash", "-c", c], capture_output=True, text=True).stdout
    return {"loat": run("loat --mode termination --proof /bench/Integer_Transition_Systems/From_T2/polyrank1.t2.ari 2>&1 | grep -A6 '^LoAT:'"), "koat2": run("koat2 --version 2>&1 | grep -i version"), "bun": run("bun --version")}


@app.local_entrypoint()
def main(out: str, tools: str = "gdp,loat,loat-abmc,koat2", limit: int = 60, sample: int = 0, only: str = "", env: str = "", tasks_file: str = ""):
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
        (outdir / "versions.json").write_text(json.dumps({**versions.remote(), "tpdb_ari": ARI_COMMIT, "loat_release": LOAT, "koat2_release": KOAT, "limit": limit, "tools": tools}, indent=1))
        chosen = [t for t in all_tasks if any(o in t["task"] for o in only.split("|"))]
        if tasks_file:
            names = set(pathlib.Path(tasks_file).read_text().split())
            chosen = [t for t in chosen if t["task"] in names]
        if sample:
            step = max(1, len(chosen) // sample)
            chosen = chosen[::step][:sample]
        shards = [(tool, [t], limit, env) for tool in tools.split(",") for t in chosen]
        print(f"{len(chosen)} tasks, {len(shards)} containers", flush=True)
        n = 0
        with (outdir / "results.jsonl").open("w") as f:
            for rows in shard.starmap(shards, order_outputs=False, return_exceptions=True):
                if isinstance(rows, BaseException):
                    rows = [{"tool": "?", "task": "?", "answer": "error", "err": repr(rows)[:400]}]
                for r in rows:
                    f.write(json.dumps(r) + "\n")
                f.flush()
                n += 1
                if n % 200 == 0:
                    print(f"{n}/{len(shards)}, {round(time.time() - t0)} s", flush=True)
    finally:
        ticket.unlink(missing_ok=True)
    print(f"done in {round(time.time() - t0, 1)} s wall")
