"""Each IC3Syn port against its TLA+ source, one protocol a 2 vCPU, 4 GB slot (a boat item, or a Modal container): TLC on
the Endive spec (at 8b6f2ab) with the port's cfg (check.ts --cfg), and check.ts's BFS of the port and of its broken
variant on the same instance.

    python3 research/protocols/ic3syn/tlc.py --only id,id --out runs/ic3syn/<name> [--ms 120000] [--backend boat|auto|modal]
    modal run research/protocols/ic3syn/tlc.py --only id,id --out runs/ic3syn/<name>          (Modal, as before)

--backend boat (the default) runs each protocol as a boat item (supercomputer/fanout.py; Temurin 17 from the image's
langs layer, Endive and tla2tools.jar fetched once per VM into ~/.cache/gdp-wired/tlc), auto falls back to Modal, modal
is `modal run`'s (OpenJDK 17, both baked into its image). <out>/results.jsonl: one JSON line per protocol, TLC's distinct
states, depth and verdict beside the port's states, depth and `bad` count.
"""
import json
import os
import pathlib
import re
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parents[2] if len(HERE.parents) > 2 else HERE  # (in the container the file is /root/tlc.py)
try:
    import modal
except ImportError:  # plain python3, --backend boat: the function runs on boat VMs (supercomputer/fanout.py)
    import sys
    sys.path.insert(0, str(GDP / "supercomputer"))
    from agent import modal_stub
    modal = modal_stub()
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
    .add_local_dir(GDP, "/src/gdp-wired", ignore=[".git/**", "**/.git", "**/node_modules/**", "**/runs/**", "supercomputer/**", "modal/**", "modal", "private/**", "vendor/**", "lean-kernel/**", "docs/**", "static/**", "examples/**", "packages/**"])
)
app = modal.App("gdp-wired-laneA-tlc", image=image)
JAR = "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
BOAT = {"path": ["/usr/lib/jvm/temurin-17/bin"]}


def assets() -> tuple[str, str]:
    """Endive's checkout and TLC's jar: the Modal image's, else fetched once per boat VM (Endive's benchmarks at the
    commit, the jar of the release), each item a copy of its own."""
    if os.path.exists("/endive"):
        return "/endive", "/tla2tools.jar"
    d = pathlib.Path.home() / ".cache" / "gdp-wired" / "tlc" / f"{ENDIVE[:12]}-v1.8.0"
    if not (d / "ok").exists():
        tmp = d.parent / f".{d.name}.{os.getpid()}"
        subprocess.run(["bash", "-c", f"set -e; rm -rf {tmp}; mkdir -p {tmp}/endive && curl -fsSL --retry 5 https://codeload.github.com/will62794/endive/tar.gz/{ENDIVE}"
                        f" | tar xz -C {tmp}/endive --strip-components 1 endive-{ENDIVE}/benchmarks && curl -fsSL --retry 5 -o {tmp}/tla2tools.jar {JAR} && touch {tmp}/ok"], check=True)
        try:
            tmp.rename(d)
        except OSError:  # (another item got there first)
            subprocess.run(["rm", "-rf", str(tmp)])
    return str(d / "endive"), str(d / "tla2tools.jar")


def sh(cmd: str, cwd: str, limit: int) -> tuple[int, str]:
    p = subprocess.run(["bash", "-c", f"timeout -s KILL {limit} {cmd}"], cwd=cwd, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


@app.function(scaledown_window=2, cpu=2.0, memory=4096, timeout=1500)
def one(pid: str, ms: int) -> dict:
    out: dict = {"id": pid}
    src = "/src/gdp-wired"
    subprocess.run(["mkdir", "-p", "/tmp/cfg"])
    code, text = sh(f"bun research/protocols/ic3syn/check.ts --only '{pid}' --cfg /tmp/cfg", src, 60)
    meta = next((json.loads(l) for l in text.splitlines() if l.startswith("{")), None)
    if not meta:
        return {**out, "error": text[-1500:]}
    if meta.get("module"):
        endive, jar = assets()
        subprocess.run(["bash", "-c", f"rm -rf /tmp/w && cp -r {endive}/benchmarks /tmp/w"])
        for fix in meta["fix"]:
            subprocess.run(["bash", "-c", fix], cwd="/tmp/w")
        code, text = sh(f"java -Xmx3g -XX:+UseParallelGC -cp {jar} tlc2.TLC -deadlock -workers 2 -metadir /tmp/meta -dump dot /tmp/graph -config /tmp/cfg/{pid}.cfg {meta['module']}.tla", "/tmp/w", 600)
        m = re.findall(r"([\d,]+) distinct states found", text)
        d = re.search(r"depth of the complete state graph search is (\d+)", text)
        out["tlc"] = {"states": int(m[-1].replace(",", "")) if m else None, "depth": int(d.group(1)) if d else None,
                      "violated": bool(re.search(r"Invariant \S+ is violated", text)), "exit": code}
        try:  # (the state graph's distinct edges between two different states: TLC's -dump dot)
            seen = set()
            for line in open("/tmp/graph.dot"):
                e = re.match(r"\s*(-?\d+) -> (-?\d+)", line)
                if e and e.group(1) != e.group(2):
                    seen.add((e.group(1), e.group(2)))
            out["tlc"]["edges"] = len(seen)
        except OSError:
            pass
        if not m or code not in (0, 12):
            out["tlc"]["tail"] = text[-1200:]
    for broken in (False, True):
        code, text = sh(f"bun research/protocols/ic3syn/check.ts --only '{pid}' --ms {ms}{' --broken' if broken else ' --edges'}", src, ms // 1000 + 60)
        line = next((json.loads(l) for l in text.splitlines() if l.startswith("{")), None)
        out["broken" if broken else "port"] = line if line else {"error": text[-1500:], "exit": code}
    return out


@app.local_entrypoint()
def main(only: str, out: str, ms: int = 120000):
    import sys
    sys.path.insert(0, str(GDP / "supercomputer"))
    import fanout
    run(fanout.ModalEx(app), only, out, ms)


def run(ex, only: str, out: str, ms: int = 120000):
    ids = [x for x in only.split(",") if x]
    path = pathlib.Path(out) / "results.jsonl"
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("w") as f:
            for r in ex.starmap(one, [(i, ms) for i in ids]):
                r = r if isinstance(r, dict) else {"error": repr(r)[:800]}
                f.write(json.dumps(r) + "\n")
                f.flush()
                print(json.dumps(r)[:600])
    finally:
        ex.close()


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(GDP / "supercomputer"))
    import fanout
    if not any(a == "--backend" or a.startswith("--backend=") for a in sys.argv[1:]):
        sys.argv[1:1] = ["--backend", "boat"]  # (boat by default; auto and modal on request)
    fanout.cli(run, __file__, __doc__)
