"""Native-job TLC cross-check: no Modal, fanout, agent import or nested dispatch.

Inside a supercomputer job (after bun install --frozen-lockfile):
  python3 research/protocols/ic3syn/tlc_native.py --only consensus --ms 120000
Artifacts go to SUPERCOMPUTER_OUTPUT_DIR (or explicit --out).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shlex
import signal
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
ENDIVE = "8b6f2abd1988eeb308f965813635e9871f253e2d"
JAR_URL = "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"


def assets() -> tuple[Path, Path]:
    """Pinned source; record the actual jar hash in each result. Overrides are paired."""
    source, jar = os.environ.get("BAPA_TLC_ENDIVE"), os.environ.get("BAPA_TLC_JAR")
    if source or jar:
        if not source or not jar:
            raise ValueError("BAPA_TLC_ENDIVE and BAPA_TLC_JAR must both be set")
        pair = Path(source).resolve(), Path(jar).resolve()
        if not (pair[0] / "benchmarks").is_dir() or not pair[1].is_file():
            raise ValueError("invalid explicit TLC assets")
        return pair
    cache = Path.home() / ".cache/gdp-wired/tlc" / (ENDIVE[:12] + "-v1.8.0")
    if not (cache / "ok").is_file():
        cache.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=".native-tlc-", dir=cache.parent) as tmp:
            staging = Path(tmp) / "assets"
            (staging / "endive").mkdir(parents=True)
            archive = Path(tmp) / "endive.tar.gz"
            steps = [
                (["curl", "-fsSL", "--retry", "3", "-o", str(archive),
                  f"https://codeload.github.com/will62794/endive/tar.gz/{ENDIVE}"], 180),
                (["tar", "xzf", str(archive), "-C", str(staging / "endive"),
                  "--strip-components", "1", f"endive-{ENDIVE}/benchmarks"], 60),
                (["curl", "-fsSL", "--retry", "3", "-o", str(staging / "tla2tools.jar"), JAR_URL], 180),
            ]
            for index, (argv, seconds) in enumerate(steps):
                code, _ = command(argv, Path(tmp), seconds, Path(tmp) / f"asset-{index}.log")
                if code != 0:
                    raise ValueError(f"TLC asset step {index} exited {code}")
            (staging / "ok").write_text(ENDIVE + "\n")
            try:
                staging.rename(cache)
            except OSError:
                if not (cache / "ok").is_file():
                    raise
    return cache / "endive", cache / "tla2tools.jar"


def process_identity(pid: int) -> str | None:
    try:
        return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[19]
    except (FileNotFoundError, ProcessLookupError):
        return None


def descendants(pid: int) -> list[tuple[int, str]]:
    """Snapshot only this launched process tree; never signal by process name/group."""
    found = []
    identity = process_identity(pid)
    if identity is None:
        return found
    found.append((pid, identity))
    for children in Path(f"/proc/{pid}/task").glob("*/children"):
        try:
            for child in children.read_text().split():
                found.extend(descendants(int(child)))
        except FileNotFoundError:
            pass
    return found


def command(argv: list[str], cwd: Path, seconds: float, log: Path) -> tuple[int, str]:
    def interrupted(signum, _frame):
        raise InterruptedError(f"native wrapper received signal {signum}")

    with log.open("w") as output:
        process = subprocess.Popen(argv, cwd=cwd, stdout=output, stderr=subprocess.STDOUT)
        old = {sig: signal.signal(sig, interrupted) for sig in (signal.SIGTERM, signal.SIGINT)}
        try:
            try:
                code = process.wait(timeout=seconds)
            except subprocess.TimeoutExpired:
                code = 124
                output.write("\nNATIVE_WRAPPER_TIMEOUT\n")
        finally:
            for sig, handler in old.items():
                signal.signal(sig, handler)
            watched = []
            try:
                for pid, identity in reversed(descendants(process.pid)):
                    if process_identity(pid) != identity:
                        continue
                    try:
                        fd = os.pidfd_open(pid)
                    except ProcessLookupError:
                        continue
                    watched.append(fd)
                    if process_identity(pid) == identity:
                        try:
                            os.kill(pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                process.wait()
                for fd in watched:
                    waiter = select.poll()
                    waiter.register(fd, select.POLLIN)
                    if not waiter.poll(5000):
                        raise TimeoutError("owned descendant did not acknowledge exit")
            finally:
                for fd in watched:
                    os.close(fd)
    return code, log.read_text(errors="replace")


def record(text: str, pid: str) -> dict:
    rows = [json.loads(line) for line in text.splitlines() if line.startswith("{")]
    if len(rows) != 1 or not isinstance(rows[0], dict) or rows[0].get("id") != pid:
        raise ValueError("expected exactly one matching check.ts record")
    return rows[0]


def verdict(tlc: dict, port: dict, broken: dict, ms: int = 120000) -> list[str]:
    """Fail closed on incomplete runs; a timeout is not a protocol counterexample."""
    failures = []
    if type(tlc.get("exit")) is not int or tlc["exit"] != 0 or tlc.get("violated") is not False or tlc.get("complete") is not True:
        failures.append("TLC did not complete successfully")
    if type(tlc.get("states")) is not int or tlc.get("states", 0) <= 0:
        failures.append("TLC state count absent/empty")
    if type(tlc.get("edges")) is not int or tlc["edges"] < 0:
        failures.append("TLC edge count absent")
    if type(port.get("exit")) is not int or port["exit"] != 0 or port.get("done") is not True or type(port.get("bad")) is not int or port["bad"] != 0:
        failures.append("positive port did not finish with zero bad states")
    if port.get("edgeComplete") is not True:
        failures.append("port edge exploration truncated or unspecified")
    for label, row in [("port", port), ("broken", broken)]:
        if type(row.get("ms")) is not int or not 0 <= row["ms"] <= ms:
            failures.append(label + " exceeded its BFS budget or omitted elapsed time")
    if type(port.get("states")) is not int or port.get("states") != tlc.get("states"):
        failures.append("distinct-state mismatch")
    if type(port.get("edges")) is not int or port.get("edges") != tlc.get("edges"):
        failures.append("distinct non-stutter edge mismatch")
    if type(broken.get("exit")) is not int or broken["exit"] != 0 or broken.get("done") is not True or type(broken.get("bad")) is not int or broken.get("bad", 0) <= 0:
        failures.append("broken variant did not demonstrate a safety violation")
    return failures


def one(pid: str, ms: int, out: Path | None = None, root: Path = ROOT) -> dict:
    if not re.fullmatch(r"[A-Za-z0-9_]+", pid) or type(ms) is not int or ms <= 0:
        raise ValueError("one needs a registry id and positive millisecond budget")
    destination = out or Path(os.environ["SUPERCOMPUTER_OUTPUT_DIR"])
    destination.mkdir(parents=True, exist_ok=True)
    report: dict = {"id": pid, "status": "not-verified", "proofSearches": 0, "nestedDispatch": False}
    try:
        with tempfile.TemporaryDirectory(prefix="native-tlc-") as tmp:
            work = Path(tmp)
            cfg = work / "cfg"
            cfg.mkdir()
            code, text = command(["bun", "research/protocols/ic3syn/check.ts", "--only", pid, "--cfg", str(cfg)], root, 60, destination / "cfg.log")
            if code != 0:
                raise ValueError(f"cfg emission exited {code}")
            meta = record(text, pid)
            module = meta.get("module")
            if not isinstance(module, str) or not re.fullmatch(r"[A-Za-z0-9_-]+", module):
                raise ValueError("missing or unsupported TLC module")
            source, jar = assets()
            report["assets"] = {"endiveRequestedCommit": ENDIVE, "jarSHA256": hashlib.sha256(jar.read_bytes()).hexdigest(),
                                "explicitOverride": bool(os.environ.get("BAPA_TLC_ENDIVE"))}
            benchmarks = work / "benchmarks"
            shutil.copytree(source / "benchmarks", benchmarks)
            (destination / "metadata.json").write_text(json.dumps(meta, indent=2) + "\n")
            shutil.copyfile(cfg / f"{pid}.cfg", destination / "model.cfg")
            for i, fix in enumerate(meta.get("fix", [])):
                # Support the two repository fixture forms without starting a shell.
                here = re.fullmatch(r"cat > ([A-Za-z0-9_.-]+) <<'EOF'\n([\s\S]*)EOF", fix)
                if here:
                    (benchmarks / here.group(1)).write_text(here.group(2))
                    continue
                args = shlex.split(fix)
                if len(args) != 4 or args[0:2] != ["sed", "-i"] or not re.fullmatch(r"[A-Za-z0-9_.-]+", args[3]):
                    raise ValueError(f"unsupported repository fixture patch {i}")
                code, _ = command(args, benchmarks, 60, destination / f"fix-{i}.log")
                if code != 0:
                    raise ValueError(f"fixture patch {i} exited {code}")
            shutil.copyfile(benchmarks / (module + ".tla"), destination / "model.tla")
            graph = work / "graph"
            code, text = command(["java", "-Xmx3g", "-XX:+UseParallelGC", "-cp", str(jar), "tlc2.TLC",
                                  "-deadlock", "-workers", "2", "-metadir", str(work / "meta"),
                                  "-dump", "dot", str(graph), "-config", str(cfg / f"{pid}.cfg"), module + ".tla"],
                                 benchmarks, 600, destination / "tlc.log")
            states = re.findall(r"([\d,]+) distinct states found", text)
            depth = re.search(r"depth of the complete state graph search is (\d+)", text)
            tlc = {"exit": code, "states": int(states[-1].replace(",", "")) if states else None,
                   "depth": int(depth.group(1)) if depth else None,
                   "violated": bool(re.search(r"Invariant \S+ is violated", text)),
                   "complete": "Model checking completed. No error has been found." in text}
            if graph.with_suffix(".dot").is_file():
                edges = set()
                with graph.with_suffix(".dot").open() as file:
                    for line in file:
                        edge = re.match(r"\s*(-?\d+) -> (-?\d+)", line)
                        if edge and edge.group(1) != edge.group(2):
                            edges.add((edge.group(1), edge.group(2)))
                tlc["edges"] = len(edges)
            report["tlc"] = tlc
            for negative in (False, True):
                label = "broken" if negative else "port"
                argv = ["bun", "research/protocols/ic3syn/check.ts", "--only", pid, "--ms", str(ms), "--broken" if negative else "--edges"]
                code, text = command(argv, root, ms / 1000 + 60, destination / (label + ".log"))
                report[label] = {**record(text, pid), "exit": code}
            report["failures"] = verdict(tlc, report["port"], report["broken"], ms)
            if not report["failures"]:
                report["status"] = "passed"
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    (destination / "result.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--only", required=True, help="exactly one registry id per native job")
    parser.add_argument("--ms", type=int, default=120000)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    result = one(args.only, args.ms, args.out)
    print(json.dumps(result))
    return 0 if result["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
