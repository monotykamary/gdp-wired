"""envcheck.py on Modal against a Redis 7 started in the container (the Redis checks only; the PostgreSQL and HTTP checks
need --pg, as envcheck.py says).

    modal run research/distributed/envcheck_modal.py --out runs/<lane>/envcheck.json
"""
import json
import pathlib

import modal

HERE = pathlib.Path(__file__).resolve().parent
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("redis-server")
    .pip_install("redis==5.0.8", "psycopg[binary]==3.2.3", "requests==2.32.3")
    .add_local_file(HERE / "envcheck.py", "/check/envcheck.py")
)
app = modal.App("gdp-wired-envcheck", image=image)


@app.function(scaledown_window=2, timeout=300, cpu=1.0, memory=1024)
def run() -> dict:
    import subprocess
    subprocess.run(["redis-server", "--daemonize", "yes", "--save", "", "--appendonly", "no"], check=True)
    import time
    time.sleep(0.5)
    v = subprocess.run(["redis-server", "--version"], capture_output=True, text=True).stdout.strip()
    p = subprocess.run(["timeout", "-s", "KILL", "240", "python3", "-I", "/check/envcheck.py", "--redis", "redis://127.0.0.1:6379/0", "--json", "/tmp/out.json"], capture_output=True, text=True)
    out = json.loads(pathlib.Path("/tmp/out.json").read_text()) if pathlib.Path("/tmp/out.json").exists() else []
    return {"version": v, "code": p.returncode, "stdout": p.stdout, "stderr": p.stderr[-4000:], "results": out}


@app.local_entrypoint()
def main(out: str):
    r = run.remote()
    print(r["version"]); print(r["stdout"]); print(r["stderr"])
    pathlib.Path(out).write_text(json.dumps(r, indent=1))
