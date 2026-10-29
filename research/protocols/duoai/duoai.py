"""DuoAI (Yao, Tao, Gu, Nieh, OSDI 2022) on Modal, on the shape gdp-wired's pilot uses (modal/run.py: 2 CPU, 4 GB),
each run its own container, held to a wall-time limit.

    modal run research/protocols/duoai/duoai.py --out runs/duoai/<name> [--protocols a,b] [--limits 60,10] [--runs 3] [--hard]

DuoAI's artifact has no Docker image: its README is an install script (conda, Python 2.7 with ms-ivy for ivy_check,
Python >= 3.8 with numpy, scipy and pandas, `make` in src-c/). This image follows it on Ubuntu 20.04, one of the
systems the README names, with every version pinned below: the artifact's commit, the base image's digest, Python 2.7
and 3.8 (the distribution's), ms-ivy 1.8.23 (the last Python 2 release, February 2022, before DuoAI's; its wheel
carries its own Z3, whose version the build prints) by its sha256, and the Python libraries at the README's versions.

A run: a fresh copy of the artifact, `python DuoAI.py <protocol>` in a session of its own, killed (the whole session)
at the limit. Its verdict is DuoAI's own: proven when a refinement process wrote its success signal (DuoAI.py's
`signals.txt`), which it does only once ivy_check (Ivy and Z3) found the candidate set inductive with the safety
property in it. Then, outside the timed window, the invariant file it printed is checked again with ivy_check, and the
safety property is looked for in it verbatim. Times: the wall time from the process's start to its exit (the figure
compared), DuoAI's own "DuoAI runtime" (from its object's creation), and the split at the first "All simulation
processes finished" (translation and simulation, then enumeration and refinement). The C++ is compiled once, in the
image; nothing is compiled per run.

Cost: one container per run, each function timed out at 420 s (a 60 s run, the re-checks capped at 120 s each),
every call cancelled when the client exits, `scaledown_window=2`.
"""
import json
import pathlib
import time

import modal

DUOAI = "https://github.com/VeriGu/DuoAI"
DUOAI_COMMIT = "ecd37c418ef56202ca332d5bca113e8e7c8c8fac"  # master, 2025-04-30 (8ce5ecc, 2022-07-30, plus a sampler fix)
UBUNTU = "ubuntu:20.04@sha256:8feb4d8ca5354def3d8fce243717141ce31e2c428701f6682bd2fafe15388214"
IVY_WHEEL = "ms_ivy-1.8.23-py2-none-manylinux1_x86_64.whl"
IVY_URL = "https://files.pythonhosted.org/packages/py2/m/ms-ivy/" + IVY_WHEEL
IVY_SHA256 = "95a59388d2f959015274c33cf8eba635a02875e7d6e434f707e574ee09ec426d"
# ms-ivy 1.8.23's requirements (pyparsing is its own pin), and DuoAI's README's numpy, scipy and pandas with theirs
PY2_LIBS = "pyparsing==2.1.4 ply==3.11 tarjan==0.2.3.2 pydot==1.4.2"
PY3_LIBS = "numpy==1.20.2 scipy==1.6.2 pandas==1.2.4 python-dateutil==2.8.1 pytz==2021.1 six==1.16.0"

PROTOCOLS = ["lock_server_sync", "lock_server_async", "decentralized_lock", "distributed_lock", "two_phase_commit",
             "ticket_lock", "toy_consensus_forall", "consensus_wo_decide", "ring_leader_election", "sharded_key_value_store"]

image = (
    modal.Image.from_registry(UBUNTU, add_python="3.11")  # (3.11 is Modal's own runtime; DuoAI runs on the 3.8 below)
    .env({"DEBIAN_FRONTEND": "noninteractive", "TZ": "Etc/UTC"})
    .apt_install("python2.7=2.7.18-1~20.04.7", "python2.7-minimal=2.7.18-1~20.04.7", "libpython2.7-stdlib=2.7.18-1~20.04.7",
                 "libpython2.7-minimal=2.7.18-1~20.04.7", "python3.8=3.8.10-0ubuntu1~20.04.18", "python3.8-minimal=3.8.10-0ubuntu1~20.04.18",
                 "libpython3.8-stdlib=3.8.10-0ubuntu1~20.04.18", "libpython3.8-minimal=3.8.10-0ubuntu1~20.04.18",
                 "python3-pip", "python3-distutils", "g++", "make", "git", "curl", "ca-certificates", "procps")
    .run_commands(
        "curl -fsSL https://bootstrap.pypa.io/pip/2.7/get-pip.py -o /tmp/get-pip.py && python2.7 /tmp/get-pip.py 'pip==20.3.4' 'setuptools==44.1.1' 'wheel==0.37.1'",
        f"curl -fsSL -o /tmp/{IVY_WHEEL} {IVY_URL} && echo '{IVY_SHA256}  /tmp/{IVY_WHEEL}' | sha256sum -c -",
        f"python2.7 -m pip install --no-deps /tmp/{IVY_WHEEL} {PY2_LIBS}",
        f"python3.8 -m pip install --no-deps {PY3_LIBS}",
        f"git clone {DUOAI} /opt/DuoAI && cd /opt/DuoAI && git checkout -q {DUOAI_COMMIT} && git log -1 --format='DuoAI %H %ad'",
        # DuoAI's step 3: the absolute path of ivy_check in src-c/InvRefiner.h
        "sed -i \"s|^#define IVY_CHECK_PATH .*|#define IVY_CHECK_PATH \\\"$(command -v ivy_check)\\\"|\" /opt/DuoAI/src-c/InvRefiner.h"
        " && grep -n IVY_CHECK_PATH /opt/DuoAI/src-c/InvRefiner.h",
        "cd /opt/DuoAI/src-c && make -j2 >/dev/null && ls -la main",
        "mkdir -p /opt/duobin && ln -sf /usr/bin/python3.8 /opt/duobin/python",
        # ms-ivy writes its ply parse tables into its package directory on first use (its wheel has none), so the first
        # ivy_check calls of a fresh container, which DuoAI makes four at a time, would race to write them; write them
        # once here, as one ivy_check on an installed machine leaves them
        "cd /opt/DuoAI && (ivy_check protocols/lock_server_sync/lock_server_sync.ivy >/dev/null 2>&1 || true)"
        " && ls /usr/local/lib/python2.7/dist-packages/ivy/ | grep -E 'tab\\.py$'",
        # what was installed, into the build log
        "python2.7 --version; python3.8 --version; g++ --version | head -1; dpkg-query -W python2.7 python3.8 g++",
        "python2.7 -c \"from ivy.z3 import z3; print('z3', z3.get_version_string())\"",
        "python2.7 -m pip freeze; python3.8 -m pip freeze | grep -iE 'numpy|scipy|pandas|dateutil|pytz|six'",
    )
)
app = modal.App("gdp-wired-duoai", image=image)
ENV_PATH = "/opt/duobin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"


def ivy_check(path: pathlib.Path, cwd: pathlib.Path, cap: int = 120) -> dict:
    import subprocess
    t = time.monotonic()
    try:
        p = subprocess.run(["timeout", "-s", "KILL", str(cap), "ivy_check", str(path)], cwd=cwd, capture_output=True, text=True,
                           env={"PATH": ENV_PATH, "HOME": "/root"})
        out = (p.stdout + p.stderr).strip()
        return {"file": path.name, "ok": p.returncode == 0 and out.endswith("OK"), "code": p.returncode, "seconds": round(time.monotonic() - t, 2), "tail": out[-300:]}
    except Exception as e:
        return {"file": path.name, "ok": False, "code": -1, "seconds": round(time.monotonic() - t, 2), "tail": repr(e)}


@app.function(cpu=2.0, memory=4096, timeout=420, scaledown_window=2)
def duo(protocol: str, limit: int, tag: str) -> dict:
    import os
    import re
    import shutil
    import signal
    import subprocess
    import threading

    work = pathlib.Path("/work/DuoAI")
    shutil.rmtree(work, ignore_errors=True)
    shutil.copytree("/opt/DuoAI", work, symlinks=True)
    cpuinfo = pathlib.Path("/proc/cpuinfo").read_text()
    model = next((l.split(":", 1)[1].strip() for l in cpuinfo.splitlines() if l.startswith("model name")), "?")
    env = {"PATH": ENV_PATH, "HOME": "/root", "PYTHONUNBUFFERED": "1"}

    lines: list[tuple[float, str]] = []
    t0 = time.monotonic()
    p = subprocess.Popen(["python", "DuoAI.py", protocol], cwd=work, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, errors="replace", start_new_session=True)

    def read():
        for line in p.stdout:
            lines.append((round(time.monotonic() - t0, 3), line.rstrip("\n")))
    reader = threading.Thread(target=read, daemon=True)
    reader.start()
    try:
        p.wait(timeout=limit)
        killed = False
    except subprocess.TimeoutExpired:
        killed = True
    wall = round(time.monotonic() - t0, 3)
    try:  # the whole session: samplers, the C++ processes and their ivy_check children
        os.killpg(p.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    p.wait()
    reader.join(timeout=5)
    import resource
    ru = resource.getrusage(resource.RUSAGE_CHILDREN)  # every process of the run (each waited for by its parent)
    cpu_s = round(ru.ru_utime + ru.ru_stime, 2)

    sig_file = work / "src-c" / "runtime" / protocol / "signals.txt"
    sig = sig_file.read_text().strip() if sig_file.exists() else ""
    proven = (not killed) and any(c in sig for c in "cmtb")
    text = [l for _, l in lines]
    runtime = next((float(m.group(1)) for l in text if (m := re.match(r"DuoAI runtime: ([0-9.]+)s", l))), None)
    sim_done = next((t for t, l in lines if l.startswith("All simulation processes finished")), None)

    # Outside the timed window: the invariant files DuoAI says it wrote ("Inductive invariant written to ..."), the
    # last one its final answer, each checked again by ivy_check.
    outs = sorted((work / "outputs" / protocol).glob("*.ivy"), key=lambda f: f.stat().st_mtime)
    written = list(dict.fromkeys(m.group(1) for l in text if (m := re.match(r"Inductive invariant written to (\S+)", l))))
    final = [work / written[-1]] if proven and written else []
    src = (work / "protocols" / protocol / f"{protocol}.ivy").read_text()
    safety = next((l.strip() for l in src.splitlines() if l.strip().startswith("invariant [1000000]")), "")
    recheck = None
    inv_text = ""
    if final:
        inv_text = final[0].read_text()
        recheck = ivy_check(final[0], final[0].parent)
        recheck["safety_verbatim"] = safety.split("#")[0].strip() in inv_text
        recheck["invariants"] = sum(1 for l in inv_text.splitlines() if l.strip().startswith("invariant"))
        recheck["others"] = {w: ivy_check(work / w, final[0].parent)["ok"] for w in written[:-1]}
    return {"tag": tag, "protocol": protocol, "limit": limit, "verdict": "proven" if proven else ("timeout" if killed else "failed"),
            "signal": sig, "killed": killed, "wall": wall, "cpu_seconds": cpu_s, "duoai_runtime": runtime,
            "simulate": sim_done, "refine": round(wall - sim_done, 3) if (sim_done is not None and not killed) else None,
            "final": final[0].name if final else None, "recheck": recheck, "cpu": model, "nproc": len(os.sched_getaffinity(0)),
            "outputs": [f.name for f in outs], "inv": inv_text[-20_000:], "log": "\n".join(f"{t:8.3f} {l}" for t, l in lines)[-200_000:]}


@app.local_entrypoint()
def main(out: str, protocols: str = ",".join(PROTOCOLS), limits: str = "60,10", runs: int = 3, hard: bool = False):
    # --hard: a hard cap of 2 CPUs (Modal's cpu=(request, limit)); without it, run.py's shape, cpu=2.0, which may burst
    fn = duo.with_options(cpu=(2.0, 2.0)) if hard else duo
    outdir = pathlib.Path(out)
    outdir.mkdir(parents=True, exist_ok=True)
    jobs = [(p, int(lim), r) for lim in limits.split(",") for p in protocols.split(",") for r in range(1, runs + 1)]
    calls = []
    try:
        for p, lim, r in jobs:
            tag = f"{p}-s{lim}-r{r}"
            calls.append((tag, p, lim, fn.spawn(p, lim, tag)))
        print(f"{len(calls)} runs spawned", flush=True)
        with open(outdir / "summary.tsv", "w") as tsv:
            tsv.write("tag\tprotocol\tlimit\tverdict\twall\tcpu_seconds\tduoai_runtime\tsimulate\trefine\trecheck\tsafety_verbatim\tcpu\n")
            for tag, p, lim, c in calls:
                try:
                    r = c.get(timeout=600)
                except Exception as e:  # a lost or failed container still gets a row
                    r = {"tag": tag, "protocol": p, "limit": lim, "verdict": "error", "wall": -1, "err": repr(e)}
                log = r.pop("log", "")
                inv = r.pop("inv", "")
                (outdir / f"{tag}.log").write_text(log)
                if inv:
                    (outdir / f"{tag}.inv.ivy").write_text(inv)
                (outdir / f"{tag}.json").write_text(json.dumps(r, indent=1))
                rc = r.get("recheck") or {}
                tsv.write("\t".join(str(x) for x in [tag, p, lim, r["verdict"], r.get("wall"), r.get("cpu_seconds"), r.get("duoai_runtime"), r.get("simulate"), r.get("refine"),
                                                    rc.get("ok"), rc.get("safety_verbatim"), r.get("cpu")]) + "\n")
                tsv.flush()
                print(tag, r["verdict"], r.get("wall"), "recheck", rc.get("ok"), flush=True)
    finally:  # whatever happened, nothing keeps running
        for *_, c in calls:
            try:
                c.cancel()
            except Exception:
                pass
