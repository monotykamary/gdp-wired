"""The Swift front end's jobs (core/extract-swift.ts), 8 vCPU and 16 GB a job, gdp-wired copied fresh each run with its
node modules: on a whole large boat VM (Swift 6.3.3 for Ubuntu 24.04, the image's langs layer, /opt/swift) or in a
Modal container of the official Linux image, swift:6.3.3 (Ubuntu 22.04). What the extractor caches in the temporary
directory (the reader built once per version of its source, each package's check build) is kept between jobs, so a job
rebuilds only what changed: on boat in each VM's ~/.cache/gdp-wired/swift (built by that toolchain), on Modal on the
`gdp-wired-swift` volume (built by the image's: its binaries link the image's toolchain, so they never go to boat).

  python3 research/langs/swift/modal_swift.py --cmd 'cd core && bun test extract-swift.test.ts' --timeout 900 [--backend boat|auto|modal]
  python3 research/langs/swift/modal_swift.py --jobs research/langs/swift/jobs.json --out runs/swift/<name>
  modal run research/langs/swift/modal_swift.py ...                    (Modal, as before)

--backend boat is the default, auto falls back to Modal, modal is `modal run`'s. Cost rules: scaledown_window=2, every
call sized by its own timeout (the command killed inside first, so its output still comes back), one job at a time
unless --jobs fans out; `modal app list` after a Modal batch.
"""
import json
import pathlib
import subprocess
import sys
import time

HERE = pathlib.Path(__file__).resolve().parent
try:
    import modal
except ImportError:  # plain python3, --backend boat: the jobs run on boat VMs (supercomputer/fanout.py)
    sys.path.insert(0, str(HERE.parents[2] / "supercomputer"))
    from agent import modal_stub
    modal = modal_stub()
STUB = getattr(modal, "__gdpw_stub__", False)  # (on a boat VM, and in this client without Modal)
GDP = HERE.parents[2] if STUB or modal.is_local() else pathlib.Path("/src/gdp-wired")
SWIFT = "swift:6.3.3-jammy"

image = (
    modal.Image.from_registry(SWIFT, add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "xz-utils", "git", "zstd")
    .run_commands("curl -fsSL https://bun.sh/install | bash")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_file(GDP / "package.json", "/deps/package.json", copy=True)
    .add_local_file(GDP / "bun.lock", "/deps/bun.lock", copy=True)
    .run_commands("cd /deps && bun install --frozen-lockfile >/dev/null 2>&1 || (cd /deps && bun install)")
    .add_local_dir(GDP, "/src/gdp-wired", ignore=[".git/**", "**/.git", "**/.git/**", "**/node_modules/**", "runs/**", "**/.build/**", "**/*.olean", "**/*.ilean"])
)
app = modal.App("gdp-wired-swift", image=image)
cache = modal.Volume.from_name("gdp-wired-swift", create_if_missing=True)
# a whole large VM a job (four slots: 8 vCPU, 16 GB, as the Modal function), the langs layer's Swift first on the PATH
BOAT = {"path": ["/opt/swift/usr/bin"], "weight": 4}


@app.function(scaledown_window=2, cpu=8.0, memory=16384, timeout=2400, volumes={"/cache": cache})
def run(cmd: str, limit: int = 900, save: bool = True, name: str = "") -> dict:
    t0 = time.time()
    sh = lambda c, t=600: subprocess.run(["bash", "-c", c], capture_output=True, text=True, timeout=t)
    boat = not pathlib.Path("/deps").exists()  # (a boat VM: /work is the item's own, the node modules installed here)
    vol = str(pathlib.Path.home() / ".cache/gdp-wired/swift") if boat else "/cache"
    if boat:
        sh(f"mkdir -p {vol} && cp -a /src/gdp-wired/. /work/ && cd /work && bun install --frozen-lockfile > /dev/null 2>&1", 900)
    else:
        sh("cp -r /src/gdp-wired /work && ln -s /deps/node_modules /work/node_modules")
    # (the extractor's caches: the reader's build, the packages' check builds, SwiftPM's checkouts)
    restore = sh(f"mkdir -p /tmp/gdp && if [ -f {vol}/tmp.tar.zst ]; then tar --zstd -xf {vol}/tmp.tar.zst -C / && echo restored; fi; du -sh /tmp 2>/dev/null", 600)
    r = subprocess.run(["bash", "-c", f"cd /work && timeout -s KILL {limit} bash -c {json.dumps(cmd)}"], capture_output=True, text=True)
    out = {"name": name, "code": r.returncode, "stdout": r.stdout[-60000:], "stderr": r.stderr[-20000:], "restore": restore.stdout.strip(), "secs": round(time.time() - t0, 1)}
    if save:
        s = sh(f"cd / && ls -d tmp/gdp-swift* tmp/gdp >/dev/null 2>&1 && tar --zstd -cf {vol}/tmp.tar.zst.new $(ls -d tmp/gdp-swift* 2>/dev/null) && mv {vol}/tmp.tar.zst.new {vol}/tmp.tar.zst && du -sh {vol}/tmp.tar.zst", 900)
        out["saved"] = s.stdout.strip() + s.stderr.strip()[-300:]
        if not boat:
            cache.commit()
    return out


@app.local_entrypoint()
def main(cmd: str = "", timeout: int = 900, jobs: str = "", out: str = "", save: bool = True):
    if cmd:
        # (a client-side cap too: a container that can't start must not keep the client waiting)
        call = run.spawn(cmd, timeout, save)
        try: r = call.get(timeout=timeout + 400)
        except Exception as e: call.cancel(); raise SystemExit(f"--- cancelled: {e!r}")
        show(r)
        return
    sys.path.insert(0, str(GDP / "supercomputer"))
    import fanout
    drive(fanout.ModalEx(app), "", timeout, jobs, out)


def show(r: dict):
    print(r["stdout"])
    print(r["stderr"], file=sys.stderr)
    print(f"--- exit {r['code']} in {r['secs']} s; {r['restore']}; {r.get('saved', '')}")


def drive(ex, cmd: str = "", timeout: int = 900, jobs: str = "", out: str = "", no_save: bool = False):
    try:
        if cmd:
            r = ex.remote(run, cmd, timeout, not no_save)
            show(r)
            return
        todo = json.loads(pathlib.Path(jobs).read_text())
        od = pathlib.Path(out)
        od.mkdir(parents=True, exist_ok=True)
        for r in ex.starmap(run, [(j["cmd"], j.get("timeout", timeout), False, j["name"]) for j in todo]):
            if isinstance(r, BaseException):
                print(f"a job failed on the backend: {str(r)[:400]}")
                continue
            (od / f"{r['name']}.log").write_text(r["stdout"] + "\n--- stderr\n" + r["stderr"])
            print(f"{r['name']}: exit {r['code']} in {r['secs']} s")
    finally:
        ex.close()


if __name__ == "__main__":
    sys.path.insert(0, str(GDP / "supercomputer"))
    import fanout
    if not any(a == "--backend" or a.startswith("--backend=") for a in sys.argv[1:]):
        sys.argv[1:1] = ["--backend", "boat"]  # (boat by default; auto and modal on request)
    fanout.cli(drive, __file__, __doc__)
