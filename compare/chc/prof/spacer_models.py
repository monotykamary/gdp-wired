"""The invariants Spacer finds for given tasks, to see what gdp-wired's candidates miss:
`modal run compare/chc/prof/spacer_models.py --out <dir> --tasks-json <file of task names>`. Each task's model (Z3 5.3.1,
fp.engine=spacer, 30 s) lands in <dir>/models.jsonl."""
import json
import pathlib
import re
import subprocess

import modal

from_chc = pathlib.Path(__file__).resolve().parent.parent
image = modal.Image.from_registry("ubuntu:24.04", add_python="3.12").apt_install("curl", "unzip", "ca-certificates").run_commands(
    "curl -fsSL -o /tmp/z3.zip https://github.com/Z3Prover/z3/releases/download/z3-5.3.1/z3-5.3.1-x64-glibc-2.39.zip"
    " && unzip -q /tmp/z3.zip -d /opt && ln -s /opt/z3-5.3.1-x64-glibc-2.39/bin/z3 /usr/local/bin/z3",
    "mkdir /bench && curl -fsSL https://codeload.github.com/chc-comp/chc-comp26-benchmarks/tar.gz/b4fa7a708e5863bbcdb5de50d692ead3a67cbedc | tar xz -C /bench --strip-components 1",
)
app = modal.App("gdp-wired-spacer-models", image=image)


@app.function(cpu=2.0, memory=4096, timeout=300)
def model(task: str) -> dict:
    y = pathlib.Path("/bench") / task
    smt2 = y.parent / re.search(r"^input_files:\s*(\S+)", y.read_text(), re.M).group(1)
    text = re.sub(r"\(exit\)\s*$", "", smt2.read_text().strip()) + "\n(get-model)\n"
    tmp = pathlib.Path("/tmp/t.smt2")
    tmp.write_text(text)
    try:
        p = subprocess.run(["z3", "fp.engine=spacer", "-T:30", str(tmp)], capture_output=True, text=True, timeout=60)
        out = p.stdout
    except subprocess.TimeoutExpired:
        out = "timeout"
    return {"task": task, "model": out[-6000:]}


@app.local_entrypoint()
def main(out: str, tasks_json: str):
    tasks = json.loads(pathlib.Path(tasks_json).read_text())
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    with (outdir / "models.jsonl").open("w") as f:
        for row in model.map(tasks, order_outputs=False, return_exceptions=True):
            if isinstance(row, dict):
                f.write(json.dumps(row) + "\n")
