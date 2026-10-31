"""envcheck.py against the stacks it describes, each started in the job: PostgreSQL 15, Redis 7.0.15, and urllib3 under
requests 2.32.3 (every check: --pg and --redis).

    python3 research/distributed/envcheck_modal.py --out runs/<lane>/envcheck [--backend boat|auto|modal]
    modal run research/distributed/envcheck_modal.py --out runs/<lane>/envcheck          (Modal, as before)

--backend boat (the default) runs it as a boat item (supercomputer/fanout.py): PostgreSQL 15 from conda-forge (by
micromamba), Redis 7.0.15 built from its release, the Python clients in a venv, all as the VM's user, kept once per VM in
~/.cache/gdp-wired/envcheck; auto falls back to Modal; modal is `modal run`'s (Debian 12's postgresql-15 and
redis-server, 7.0.15). <out>/envcheck.json: the versions, the exit code, the output and each check's row.
"""
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
try:
    import modal
except ImportError:  # plain python3, --backend boat: the check runs on a boat VM (supercomputer/fanout.py)
    import sys
    sys.path.insert(0, str(HERE.parent.parent / "supercomputer"))
    from agent import modal_stub
    modal = modal_stub()

PIP = ["redis==5.0.8", "psycopg[binary]==3.2.3", "requests==2.32.3"]
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("redis-server", "postgresql-15")
    .pip_install(*PIP)
    .add_local_file(HERE / "envcheck.py", "/check/envcheck.py")
)
app = modal.App("gdp-wired-envcheck", image=image)

# On a boat VM, as its user (no apt): the stacks once per VM, under a lock (two items on one VM)
REDIS = "7.0.15"
BOAT_STACKS = f"""
set -e
C=~/.cache/gdp-wired/envcheck/pg15-redis{REDIS}
mkdir -p "$(dirname $C)" && exec 9>"$C.lock" && flock 9
if [ ! -f $C/ok ]; then
  rm -rf $C && mkdir -p $C && cd $C
  curl -fsSL --retry 5 https://micro.mamba.pm/api/micromamba/linux-64/latest | tar xj bin/micromamba
  MAMBA_ROOT_PREFIX=$C/mamba ./bin/micromamba create -y -q -p $C/pg -c conda-forge 'postgresql=15' > /dev/null
  curl -fsSL --retry 5 https://download.redis.io/releases/redis-{REDIS}.tar.gz | tar xz
  make -s -C redis-{REDIS} -j2 > /dev/null 2>&1 && cp redis-{REDIS}/src/redis-server redis-{REDIS}/src/redis-cli $C/
  python3 -m venv $C/venv && $C/venv/bin/pip install -q {' '.join(repr(p) for p in PIP)}
  rm -rf redis-{REDIS} mamba bin && touch ok
fi
"""


@app.function(scaledown_window=2, timeout=900, cpu=1.0, memory=1024)
def check() -> dict:
    import socket
    import subprocess
    import time
    out_json = "/tmp/out.json"
    sh = lambda c: subprocess.run(["bash", "-c", c], capture_output=True, text=True)
    if pathlib.Path("/check/envcheck.py").exists():  # Modal's image: as root, PostgreSQL as its own user
        script, py, redis, port = "/check/envcheck.py", "python3", "redis-server", 6379
        pg = "/usr/lib/postgresql/15/bin"
        start = (f"mkdir -p /tmp/pg && chown postgres /tmp/pg && runuser -u postgres -- {pg}/initdb -D /tmp/pg/data -A trust -U postgres > /dev/null"
                 f" && runuser -u postgres -- {pg}/pg_ctl -D /tmp/pg/data -l /tmp/pg/log -o \"-k /tmp -c listen_addresses=''\" -w start")
    else:  # a boat VM: the stacks from the VM's cache, Redis on a free port (other items share the VM's network)
        s = sh(BOAT_STACKS)
        if s.returncode != 0:
            return {"code": -1, "stdout": s.stdout[-4000:], "stderr": s.stderr[-4000:], "results": []}
        c = pathlib.Path.home() / ".cache/gdp-wired/envcheck" / f"pg15-redis{REDIS}"
        script, py, redis, pg = "/src/gdp-wired/research/distributed/envcheck.py", f"{c}/venv/bin/python", f"{c}/redis-server", f"{c}/pg/bin"
        with socket.socket() as so:
            so.bind(("127.0.0.1", 0))
            port = so.getsockname()[1]
        start = f"{pg}/initdb -D /tmp/pg/data -A trust -U postgres > /dev/null && {pg}/pg_ctl -D /tmp/pg/data -l /tmp/pg/log -o \"-k /tmp -c listen_addresses=''\" -w start"
    s = sh(start)
    if s.returncode != 0:
        return {"code": -1, "stdout": s.stdout[-4000:], "stderr": s.stderr[-4000:] + sh("cat /tmp/pg/log").stdout[-2000:], "results": []}
    subprocess.run([redis, "--daemonize", "yes", "--port", str(port), "--save", "", "--appendonly", "no"], check=True)
    time.sleep(0.5)
    versions = {"redis": sh(f"{redis} --version").stdout.strip(), "postgres": sh(f"{pg}/postgres --version").stdout.strip(),
                "python": sh(f"{py} -I -c 'import sys, urllib3, requests, redis, psycopg; print(sys.version.split()[0], urllib3.__version__, requests.__version__, redis.__version__, psycopg.__version__)'").stdout.strip()}
    p = subprocess.run(["timeout", "-s", "KILL", "240", py, "-I", script, "--pg", "dbname=postgres user=postgres host=/tmp", "--redis", f"redis://127.0.0.1:{port}/0", "--json", out_json],
                       capture_output=True, text=True)
    sh(f"{redis.removesuffix('redis-server')}redis-cli -p {port} shutdown nosave; {pg}/pg_ctl -D /tmp/pg/data -m immediate stop")
    out = json.loads(pathlib.Path(out_json).read_text()) if pathlib.Path(out_json).exists() else []
    return {"versions": versions, "code": p.returncode, "stdout": p.stdout, "stderr": p.stderr[-4000:], "results": out}


@app.local_entrypoint()
def main(out: str):
    import sys
    sys.path.insert(0, str(HERE.parent.parent / "supercomputer"))
    import fanout
    run(fanout.ModalEx(app), out)


def run(ex, out: str):
    try:
        r = ex.remote(check)
    finally:
        ex.close()
    print(r.get("versions")); print(r["stdout"]); print(r["stderr"])
    pathlib.Path(out).mkdir(parents=True, exist_ok=True)
    (pathlib.Path(out) / "envcheck.json").write_text(json.dumps(r, indent=1))


if __name__ == "__main__":
    import sys
    sys.path.insert(0, str(HERE.parent.parent / "supercomputer"))
    import fanout
    if not any(a == "--backend" or a.startswith("--backend=") for a in sys.argv[1:]):
        sys.argv[1:1] = ["--backend", "boat"]  # (boat by default; auto and modal on request)
    fanout.cli(run, __file__, __doc__)
