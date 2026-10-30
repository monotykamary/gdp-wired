"""Each IC3Syn port against its TLA+ source on Modal (one container a protocol): TLC on the Endive spec (at 8b6f2ab) with
the port's cfg (check.ts --cfg), and check.ts's BFS of the port and of its broken variant on the same instance.

    modal run research/protocols/ic3syn/tlc.py --only id,id --out runs/ic3syn/<name>.jsonl [--ms 120000]

One JSON line per protocol: TLC's distinct states, depth and verdict beside the port's states, depth and `bad` count.
"""
import json
import pathlib
import re
import subprocess

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parents[2] if len(HERE.parents) > 2 else HERE  # (in the container the file is /root/tlc.py)
ENDIVE = "8b6f2abd1988eeb308f965813635e9871f253e2d"
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("curl", "unzip", "git", "ca-certificates", "openjdk-17-jre-headless")
    .run_commands(
        "curl -fsSL https://bun.sh/install | bash",
        f"git clone -q https://github.com/will62794/endive.git /endive && cd /endive && git checkout -q {ENDIVE}",
        "curl -fsSL -o /tla2tools.jar https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar",
    )
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_dir(GDP, "/src/gdp-wired", ignore=[".git/**", "**/.git", "**/node_modules/**", "**/runs/**", "modal/**", "private/**", "vendor/**", "lean-kernel/**", "docs/**", "static/**", "examples/**", "packages/**"])
)
app = modal.App("gdp-wired-laneA-tlc", image=image)


def sh(cmd: str, cwd: str, limit: int) -> tuple[int, str]:
    p = subprocess.run(["bash", "-c", f"timeout -s KILL {limit} {cmd}"], cwd=cwd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=900)
def one(pid: str, ms: int) -> dict:
    out: dict = {"id": pid}
    src = "/src/gdp-wired"
    subprocess.run(["mkdir", "-p", "/tmp/cfg"])
    code, text = sh(f"bun research/protocols/ic3syn/check.ts --only '{pid}' --cfg /tmp/cfg", src, 60)
    meta = next((json.loads(l) for l in text.splitlines() if l.startswith("{")), None)
    if not meta:
        return {**out, "error": text[-1500:]}
    if meta.get("module"):
        subprocess.run(["bash", "-c", "rm -rf /tmp/w && cp -r /endive/benchmarks /tmp/w"])
        for fix in meta["fix"]:
            subprocess.run(["bash", "-c", fix], cwd="/tmp/w")
        code, text = sh(f"java -Xmx3g -XX:+UseParallelGC -cp /tla2tools.jar tlc2.TLC -deadlock -workers 2 -metadir /tmp/meta -config /tmp/cfg/{pid}.cfg {meta['module']}.tla", "/tmp/w", 600)
        m = re.findall(r"([\d,]+) distinct states found", text)
        d = re.search(r"depth of the complete state graph search is (\d+)", text)
        out["tlc"] = {"states": int(m[-1].replace(",", "")) if m else None, "depth": int(d.group(1)) if d else None,
                      "violated": bool(re.search(r"Invariant \S+ is violated", text)), "exit": code}
        if not m or code not in (0, 12):
            out["tlc"]["tail"] = text[-1200:]
    for broken in (False, True):
        code, text = sh(f"bun research/protocols/ic3syn/check.ts --only '{pid}' --ms {ms}{' --broken' if broken else ''}", src, ms // 1000 + 60)
        line = next((json.loads(l) for l in text.splitlines() if l.startswith("{")), None)
        out["broken" if broken else "port"] = line if line else {"error": text[-1500:], "exit": code}
    return out


@app.local_entrypoint()
def main(only: str, out: str, ms: int = 120000):
    ids = [x for x in only.split(",") if x]
    path = pathlib.Path(out)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w") as f:
        for r in one.map(ids, kwargs={"ms": ms}, order_outputs=False, return_exceptions=True):
            r = r if isinstance(r, dict) else {"error": repr(r)[:800]}
            f.write(json.dumps(r) + "\n")
            f.flush()
            print(json.dumps(r)[:600])
