"""The Swift front end's jobs on Modal (core/extract-swift.ts): one container in the official Linux image, swift:6.3.3
(Ubuntu 22.04), with bun and the repository's node modules, gdp-wired copied fresh each run. What the extractor caches
in the temporary directory (the reader built once per version of its source, each package's check build) is kept on
the `gdp-wired-swift` volume between jobs, so a job rebuilds only what changed.

  modal run research/langs/swift/modal_swift.py --cmd 'cd core && bun test extract-swift.test.ts' --timeout 900
  modal run research/langs/swift/modal_swift.py --jobs research/langs/swift/jobs.json --out runs/swift/<name>

Cost rules: scaledown_window=2, every call sized by its own timeout (the command killed inside first, so its output
still comes back), one job at a time unless --jobs fans out; `modal app list` after every batch.
"""
import json
import pathlib
import subprocess
import sys
import time

import modal

HERE = pathlib.Path(__file__).resolve().parent
GDP = HERE.parents[2] if modal.is_local() else pathlib.Path("/src/gdp-wired")
SWIFT = "swift:6.3.3-jammy"

image = (
    modal.Image.from_registry(SWIFT, add_python="3.12")
    .apt_install("curl", "unzip", "ca-certificates", "xz-utils", "git", "zstd")
    .run_commands("curl -fsSL https://bun.sh/install | bash")
    .env({"PATH": "/root/.bun/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"})
    .add_local_file(GDP / "package.json", "/deps/package.json", copy=True)
    .add_local_file(GDP / "bun.lock", "/deps/bun.lock", copy=True)
    .run_commands("cd /deps && bun install --frozen-lockfile >/dev/null 2>&1 || (cd /deps && bun install)")
    .add_local_dir(GDP, "/src/gdp-wired", ignore=[".git/**", "**/.git", "**/.git/**", "**/node_modules/**", "**/runs/**", "**/.build/**", "**/*.olean", "**/*.ilean",
                                                  "vendor/**", "compare/**", "static/**", "docs/**", "examples/**", "lean-kernel/**/*.lean"])
)
app = modal.App("gdp-wired-swift", image=image)
cache = modal.Volume.from_name("gdp-wired-swift", create_if_missing=True)


@app.function(scaledown_window=2, cpu=8.0, memory=16384, timeout=2400, volumes={"/cache": cache})
def run(cmd: str, limit: int = 900, save: bool = True) -> dict:
    t0 = time.time()
    sh = lambda c, t=600: subprocess.run(["bash", "-c", c], capture_output=True, text=True, timeout=t)
    sh("cp -r /src/gdp-wired /work && ln -s /deps/node_modules /work/node_modules")
    # (the extractor's caches: the reader's build, the packages' check builds, SwiftPM's checkouts)
    restore = sh("mkdir -p /tmp/gdp && if [ -f /cache/tmp.tar.zst ]; then tar --zstd -xf /cache/tmp.tar.zst -C / && echo restored; fi; du -sh /tmp 2>/dev/null", 600)
    r = subprocess.run(["bash", "-c", f"cd /work && timeout -s KILL {limit} bash -c {json.dumps(cmd)}"], capture_output=True, text=True)
    out = {"code": r.returncode, "stdout": r.stdout[-60000:], "stderr": r.stderr[-20000:], "restore": restore.stdout.strip(), "secs": round(time.time() - t0, 1)}
    if save:
        s = sh("cd / && ls -d tmp/gdp-swift* tmp/gdp >/dev/null 2>&1 && tar --zstd -cf /cache/tmp.tar.zst.new $(ls -d tmp/gdp-swift* 2>/dev/null) && mv /cache/tmp.tar.zst.new /cache/tmp.tar.zst && du -sh /cache/tmp.tar.zst", 900)
        out["saved"] = s.stdout.strip() + s.stderr.strip()[-300:]
        cache.commit()
    return out


@app.local_entrypoint()
def main(cmd: str = "", timeout: int = 900, jobs: str = "", out: str = "", save: bool = True):
    if cmd:
        # (a client-side cap too: a container that can't start must not keep the client waiting)
        call = run.spawn(cmd, timeout, save)
        try: r = call.get(timeout=timeout + 400)
        except Exception as e: call.cancel(); raise SystemExit(f"--- cancelled: {e!r}")
        print(r["stdout"])
        print(r["stderr"], file=sys.stderr)
        print(f"--- exit {r['code']} in {r['secs']} s; {r['restore']}; {r.get('saved', '')}")
        return
    todo = json.loads(pathlib.Path(jobs).read_text())
    od = pathlib.Path(out)
    od.mkdir(parents=True, exist_ok=True)
    for j, r in zip(todo, run.map([j["cmd"] for j in todo], [j.get("timeout", timeout) for j in todo], [False] * len(todo))):
        (od / f"{j['name']}.log").write_text(r["stdout"] + "\n--- stderr\n" + r["stderr"])
        print(f"{j['name']}: exit {r['code']} in {r['secs']} s")
