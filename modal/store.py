"""Volumes on boat, for any project: a named set of files kept as a boat named snapshot, with a sha256 manifest,
served over a token-gated HTTPS URL, and pulled into a consumer-side cache by hash. The store imports nothing of
gdp-wired's (boat.py's CLI helpers only).

    python3 modal/store.py push <name> <dir | modal:<volume>[/path]> [--form snapshot|layer] [--max-gb 4]
    python3 modal/store.py serve <name> [--minutes 30]       a VM from the snapshot; its URL on stdout (a secret)
    python3 modal/store.py pull <name> <dest> --url URL [--cache DIR]
    python3 modal/store.py verify <name> <dir> | ls | unserve [name] [--all]

The forms: `snapshot` (an archive, or data a job fetches: about $0.056 a day a named snapshot) and `layer` (a
read-mostly cache or toolchain meant to be built into a pool image: the same snapshot, its files at /store/<name>, to
`boat new --from` or to stack under an image's layers). Either way the files are at ~/store/<name> on a VM started
from it, beside manifest.json: {path: [size, sha256]}.

push: a VM (one start) gets the files (from a directory here, or a Modal volume fetched here first: its size is
checked, at most --max-gb pass through this machine), checks every sha256 against the manifest made here, is saved as
the named snapshot `store-<name>`, and is deleted. serve: a VM from the snapshot (a start) serves ~/store/<name> on
localhost behind `boat host --private` (boat's token in the URL) under a random path of ours, for --minutes, then
stops. pull: the manifest, then each file whose sha256 the cache (~/.cache/supercomputer/store/<sha256>) lacks,
checked as it lands; the destination gets links to the cache. Modal and RunPod jobs pull the same way (python3, the
standard library), so boat is their mirror.
"""
import argparse
import base64
import contextlib
import hashlib
import json
import os
import pathlib
import secrets
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import boat  # noqa: E402  (its CLI wrappers and the pool's .live directory)

STORE = boat.LIVE / "store"
CACHE = pathlib.Path(os.environ.get("SUPERCOMPUTER_STORE_CACHE") or pathlib.Path.home() / ".cache" / "supercomputer" / "store")


def log(*a):
    print("[store]", *a, file=sys.stderr, flush=True)


def sha256(p: pathlib.Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def manifest(d: pathlib.Path) -> dict:
    return {str(p.relative_to(d)): [p.stat().st_size, sha256(p)] for p in sorted(d.rglob("*")) if p.is_file() and p.name != "manifest.json"}


CHECK = r"""
import hashlib, json, pathlib, sys
d = pathlib.Path(sys.argv[1]); want = json.loads((d / "manifest.json").read_text())
def h(p):
    x = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""): x.update(b)
    return x.hexdigest()
have = {str(p.relative_to(d)): [p.stat().st_size, h(p)] for p in sorted(d.rglob("*")) if p.is_file() and p.name != "manifest.json"}
bad = sorted(k for k in set(want) | set(have) if want.get(k) != have.get(k))
print(json.dumps({"files": len(have), "bytes": sum(v[0] for v in have.values()), "bad": bad[:20], "nbad": len(bad)}))
"""


def new_vm(src: str | None = None, ttl: int = 3600) -> str:
    out = boat.boat("new", *(["--from", src] if src else []), "--ttl", str(ttl), "--no-env", "--no-monitoring", "--json", timeout=900)
    vm = next((json.loads(l)["id"] for l in out.splitlines() if l.strip().startswith("{") and json.loads(l).get("id")), None)
    if not vm or not boat.wait_running([vm], 600):
        raise RuntimeError(f"no VM came up: {out[-300:]}")
    boat.note_starts(1)
    return vm


def from_modal(spec: str, max_gb: float) -> pathlib.Path:
    """A Modal volume (or a path in it) into a temporary directory here, once its size is known to be small enough."""
    vol, _, path = spec.removeprefix("modal:").partition("/")
    listing = json.loads(subprocess.run(["modal", "volume", "ls", vol, "/" + path, "--json"], capture_output=True, text=True, check=True).stdout or "[]")
    tmp = pathlib.Path(tempfile.mkdtemp(prefix=f"store-{vol}-", dir=os.environ.get("SUPERCOMPUTER_TMP")))
    subprocess.run(["modal", "volume", "get", vol, "/" + path, str(tmp), "--force"], check=True, capture_output=True, timeout=3600)
    size = sum(p.stat().st_size for p in tmp.rglob("*") if p.is_file())
    log(f"{spec}: {len(listing)} entries at its top, {size / 1e9:.2f} GB fetched")
    if size > max_gb * 1e9:
        shutil.rmtree(tmp)
        raise SystemExit(f"{spec} is {size / 1e9:.1f} GB: past --max-gb, it should go from Modal to boat directly")
    return tmp


def push(name: str, src: str, form: str = "snapshot", max_gb: float = 4.0):
    d = from_modal(src, max_gb) if src.startswith("modal:") else pathlib.Path(src)
    m = manifest(d)
    size = sum(v[0] for v in m.values())
    if size > max_gb * 1e9:
        raise SystemExit(f"{d} is {size / 1e9:.1f} GB: past --max-gb")
    log(f"{name}: {len(m)} files, {size / 1e6:.1f} MB from {src}")
    vm = new_vm()
    try:
        (d / "manifest.json").write_text(json.dumps(m))
        tar = subprocess.Popen(["tar", "-C", str(d), "-cf", "-", "."], stdout=subprocess.PIPE, env={**os.environ, "COPYFILE_DISABLE": "1"})  # (no macOS ._ files)
        p = subprocess.run([boat.BOAT, "ssh", vm, "--", f"sudo mkdir -p /store/{name} && sudo chown $(id -un) /store/{name} && tar -C /store/{name} -xf -"],
                           stdin=tar.stdout, capture_output=True, env=boat.ENV, timeout=7200)
        tar.wait()
        if p.returncode != 0:
            raise RuntimeError(f"upload: {p.stderr.decode()[-300:]}")
        b64 = base64.b64encode(CHECK.encode()).decode()
        r = subprocess.run([boat.BOAT, "ssh", vm, "--", f"echo {b64} | base64 -d > /tmp/check.py && python3 /tmp/check.py /store/{name}"], capture_output=True, text=True, env=boat.ENV, timeout=3600)
        if not r.stdout.strip():
            raise RuntimeError(f"the check on the VM said nothing: {r.stderr[-300:]}")
        check = json.loads(r.stdout.strip().splitlines()[-1])
        if check["nbad"] or check["files"] != len(m):
            raise RuntimeError(f"the VM's copy differs: {check}")
        log(f"{name}: on {vm}, {check['files']} files, every sha256 as here; saving store-{name}")
        boat.boat("snapshot", vm, f"store-{name}", "--json", timeout=3600)
        for _ in range(360):
            s = boat.named_snapshots().get(f"store-{name}")
            if s and s.get("status") == "ready":
                break
            time.sleep(10)
        else:
            raise RuntimeError("the snapshot isn't ready")
    finally:
        boat.boat("delete", vm, "--yes", "--json", check=False, timeout=300)
        (d / "manifest.json").unlink(missing_ok=True)
        if src.startswith("modal:"):
            shutil.rmtree(d, ignore_errors=True)
    STORE.mkdir(parents=True, exist_ok=True)
    (STORE / f"{name}.json").write_text(json.dumps({"name": name, "form": form, "snapshot": f"store-{name}", "source": src, "files": m, "bytes": size, "created": time.time()}, indent=1))
    print(f"store-{name}: {len(m)} files, {size / 1e6:.1f} MB ({form})")


def serve(name: str, minutes: int = 30) -> str:
    vm = new_vm(f"store-{name}", ttl=minutes * 60)
    tok = secrets.token_urlsafe(24)
    # (a VM from a snapshot fills its disk lazily: a file read before it's there came out cut short, so every file is
    # read once first)
    subprocess.run([boat.BOAT, "ssh", vm, "--", f"find /store/{name} -type f -exec cat {{}} + > /dev/null"], capture_output=True, env=boat.ENV, timeout=3600)
    boat.exec_(vm, ["bash", "-c", f"mkdir -p ~/srv && ln -sfn /store/{name} ~/srv/{tok} && (setsid nohup python3 -m http.server 8766 --bind 127.0.0.1 --directory ~/srv > /dev/null 2>&1 &)"], 60)
    h = boat.bj("host", vm, "8766", "--localhost", "--private")
    u = urllib.parse.urlparse(h["url"])
    url = urllib.parse.urlunparse(u._replace(path=f"/{tok}/"))
    (STORE / "serving").mkdir(parents=True, exist_ok=True)
    (STORE / "serving" / f"{vm}.json").write_text(json.dumps({"vm": vm, "name": name, "until": time.time() + minutes * 60}))
    log(f"{name}: served from {vm} for {minutes} minutes (the URL is a secret: boat's token and ours); `unserve` deletes it")
    print(url)
    return url


def pull(name: str, dest: str, url: str, cache: pathlib.Path = CACHE) -> dict:
    """The volume into dest, each file fetched only when the cache lacks its sha256 (and checked as it lands)."""
    # (boat's token is in the URL's query: its first answer sets a cookie and redirects, so a cookie jar, and the query kept)
    import http.cookiejar
    opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(http.cookiejar.CookieJar()))
    u = urllib.parse.urlparse(url)
    get = lambda path: opener.open(urllib.parse.urlunparse(u._replace(path=u.path.rstrip("/") + "/" + urllib.parse.quote(path))), timeout=600)
    m = json.loads(get("manifest.json").read())
    cache.mkdir(parents=True, exist_ok=True)
    d, fetched = pathlib.Path(dest), 0
    for path, (size, digest) in m.items():
        c = cache / digest
        for k in range(6):  # (boat's front cuts a stream now and then: the file again, whole)
            if c.exists():
                break
            tmp = cache / f".{digest}.part"
            h = hashlib.sha256()
            try:
                with get(path) as r, open(tmp, "wb") as f:
                    for b in iter(lambda: r.read(1 << 20), b""):
                        h.update(b)
                        f.write(b)
            except Exception as e:
                log(f"{path}: {str(e)[:120]}; again")
                time.sleep(1 + 2 * k)
                continue
            if h.hexdigest() == digest:
                tmp.rename(c)
                fetched += size
            else:
                tmp.unlink()
        if not c.exists():
            raise RuntimeError(f"{path}: not fetched whole with its manifest's sha256")
        out = d / path
        out.parent.mkdir(parents=True, exist_ok=True)
        with contextlib.suppress(FileNotFoundError):
            out.unlink()
        try:
            os.link(c, out)
        except OSError:
            shutil.copy2(c, out)
    log(f"{name}: {len(m)} files into {dest}, {fetched / 1e6:.1f} MB fetched, the rest from the cache")
    return m


def unserve(name: str = "", all_: bool = False):
    """Deletes the VMs `serve` started (of a name, or those past their minutes, or all)."""
    for f in sorted((STORE / "serving").glob("*.json")) if (STORE / "serving").exists() else []:
        s = json.loads(f.read_text())
        if all_ or s["name"] == name or s["until"] < time.time():
            boat.boat("delete", s["vm"], "--yes", "--json", check=False, timeout=300)
            f.unlink()
            log(f"{s['name']}: {s['vm']} deleted")


def verify(name: str, d: str) -> bool:
    want = json.loads((STORE / f"{name}.json").read_text())["files"]
    have = manifest(pathlib.Path(d))
    bad = sorted(k for k in set(want) | set(have) if want.get(k) != have.get(k))
    print(f"{name}: {len(have)} files here, {len(want)} in the manifest, {len(bad)} differ" + (f": {bad[:10]}" if bad else ""))
    return not bad


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("push")
    s.add_argument("name")
    s.add_argument("src")
    s.add_argument("--form", default="snapshot", choices=["snapshot", "layer"])
    s.add_argument("--max-gb", type=float, default=4.0)
    s = sub.add_parser("serve")
    s.add_argument("name")
    s.add_argument("--minutes", type=int, default=30)
    s = sub.add_parser("pull")
    s.add_argument("name")
    s.add_argument("dest")
    s.add_argument("--url", required=True)
    s.add_argument("--cache", default=str(CACHE))
    s = sub.add_parser("verify")
    s.add_argument("name")
    s.add_argument("dir")
    sub.add_parser("ls")
    s = sub.add_parser("unserve")
    s.add_argument("name", nargs="?", default="")
    s.add_argument("--all", action="store_true")
    a = ap.parse_args()
    if a.cmd == "push":
        push(a.name, a.src, a.form, a.max_gb)
    elif a.cmd == "serve":
        serve(a.name, a.minutes)
    elif a.cmd == "pull":
        pull(a.name, a.dest, a.url, pathlib.Path(a.cache))
    elif a.cmd == "unserve":
        unserve(a.name, a.all)
    elif a.cmd == "verify":
        sys.exit(0 if verify(a.name, a.dir) else 1)
    elif a.cmd == "ls":
        snaps = boat.named_snapshots()
        for f in sorted(STORE.glob("*.json")) if STORE.exists() else []:
            m = json.loads(f.read_text())
            print(f"{m['name']:32} {m['form']:8} {len(m['files']):6} files {m['bytes'] / 1e6:9.1f} MB  {m['snapshot']} ({snaps.get(m['snapshot'], {}).get('status', 'missing')})  from {m['source']}")
