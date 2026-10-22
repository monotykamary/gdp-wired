"""The invariants Spacer finds for given tasks, to see what gdp-wired's candidates miss:
`modal run compare/chc/prof/spacer_models.py --out <dir> --tasks-json <file of task names> [--engine z3|golem] [--limit 60]`.
Each task's model (Z3 5.3.1, fp.engine=spacer) lands in <dir>/models.jsonl, whole (up to 2 MB). With --engine golem,
Golem 0.9.0's --print-witness instead: for an unsat task, the derivation of false it found (its counterexample). The
app id and client pid are registered in modal/.live/ (modal/reap.sh stops an orphan)."""
import json
import os
import pathlib
import re
import subprocess

import modal

GDP = pathlib.Path(__file__).resolve().parent.parent.parent.parent
image = modal.Image.from_registry("ubuntu:24.04", add_python="3.12").apt_install("curl", "unzip", "ca-certificates", "bzip2").run_commands(
    "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
    " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3",
    "curl -fsSL https://github.com/usi-verification-and-security/golem/releases/download/v0.9.0/golem-x64-linux.tar.bz2"
    " | tar xj -C /opt && find /opt -name golem -type f -exec ln -s {} /usr/local/bin/golem \\; && golem --version",
    "mkdir /bench && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc | tar xz -C /bench --strip-components 1",
)
app = modal.App("gdp-wired-spacer-models", image=image)


@app.function(cpu=2.0, memory=4096, timeout=300)
def model(task: str, engine: str, limit: int) -> dict:
    y = pathlib.Path("/bench") / task
    smt2 = y.parent / re.search(r"^input_files:\s*(\S+)", y.read_text(), re.M).group(1)
    if engine == "golem":
        cmd = ["timeout", str(limit), "golem", "--print-witness", str(smt2)]
    else:
        text = re.sub(r"\(exit\)\s*$", "", smt2.read_text().strip()) + "\n(get-model)\n"
        tmp = pathlib.Path("/tmp/t.smt2")
        tmp.write_text(text)
        cmd = ["z3", "fp.engine=spacer", f"-T:{limit}", str(tmp)]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=limit + 30)
        out = p.stdout
    except subprocess.TimeoutExpired:
        out = "timeout"
    return {"task": task, "engine": engine, "chars": len(out), "model": out[:2_000_000]}


@app.local_entrypoint()
def main(out: str, tasks_json: str, engine: str = "z3", limit: int = 60):
    live = GDP / "modal" / ".live"
    live.mkdir(exist_ok=True)
    ticket = live / f"{app.app_id}"
    ticket.write_text(str(os.getpid()))
    try:
        tasks = json.loads(pathlib.Path(tasks_json).read_text())
        outdir = pathlib.Path(out)
        outdir.mkdir(parents=True, exist_ok=True)
        with (outdir / "models.jsonl").open("w") as f:
            for row in model.starmap([(t, engine, limit) for t in tasks], order_outputs=False, return_exceptions=True):
                if isinstance(row, dict):
                    f.write(json.dumps(row) + "\n")
    finally:
        ticket.unlink(missing_ok=True)
