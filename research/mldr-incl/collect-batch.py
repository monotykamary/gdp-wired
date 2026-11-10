"""Read-only, single-shot recovery of lane E's registered batch artifacts.

Bulky logs go to files, never through the bounded shell-output JSON channel.
No submit, close, cancel, or scheduler-policy operation is permitted here.
"""
import gzip
import hashlib
import io
import json
from pathlib import Path
import sys
import tarfile

from supercomputer.scheduler import Client

NAMES = {
    "integrated-check", "original-r1", "original-r2", "original-r3",
    "fresh-conditional-and-replay",
}


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    pending = path.with_name(path.name + ".collecting")
    pending.write_bytes(data)
    pending.replace(path)


def recover(batch, directory):
    client = Client()
    rows = client.req("/poll", {"batch": batch, "since": 0, "wait": 15}, timeout=35)
    if rows.get("err"):
        raise RuntimeError(rows["err"])
    if len(rows.get("rows", [])) > len(NAMES):
        raise RuntimeError("unexpected row count")
    for row in rows.get("rows", []):
        if row.get("name") not in NAMES:
            raise RuntimeError("unexpected job name")
    save(directory / "file-collection-rows.json", (json.dumps(rows, indent=2) + "\n").encode())
    data = client.req("/logs", {"batch": batch, "vms": []}, raw=True, timeout=45)
    if len(data) > 500_000_000:
        raise RuntimeError("archive exceeds local evidence allowance; leave it on boat")
    archive_hash = hashlib.sha256(data).hexdigest()
    save(directory / "recovered-logs.tar.gz", data)
    recovered = []
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as archive:
        members = {member.name: member for member in archive.getmembers() if member.isfile()}
        for row in rows.get("rows", []):
            name = row["name"]
            run = row.get("run_name") or name
            parts = []
            for stream in ("out", "err"):
                member = members.get(run + "/" + stream)
                if member is None:
                    parts.append(b"")
                else:
                    if member.size > 100_000_000:
                        raise RuntimeError("unexpectedly large log member")
                    source = archive.extractfile(member)
                    if source is None:
                        raise RuntimeError("unreadable log member")
                    parts.append(source.read())
            if not any(parts):
                raise RuntimeError("missing completed log: " + name)
            text = parts[0] + b"\n--- stderr ---\n" + parts[1]
            save(directory / (name + ".log"), text)
            compressed = gzip.compress(text, mtime=0)
            save(directory / (name + ".log.gz"), compressed)
            recovered.append({"name": name, "code": row["code"],
                              "sha256": hashlib.sha256(text).hexdigest(),
                              "gzipSha256": hashlib.sha256(compressed).hexdigest()})
    receipt = {"batch": batch, **rows, "logArchiveSha256": archive_hash,
               "logArchiveBytes": len(data), "recoveredLogs": recovered,
               "readOnly": True}
    save(directory / "file-collection.json", (json.dumps(receipt, indent=2) + "\n").encode())
    print(json.dumps({"batch": batch, "done": rows.get("done"),
                      "running": rows.get("running"), "queued": rows.get("queued"),
                      "recovered": [{"name": row["name"], "code": row["code"]}
                                    for row in rows.get("rows", [])],
                      "archiveBytes": len(data)}))


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: collect-batch.py BATCH OUTPUT_DIRECTORY")
    recover(sys.argv[1], Path(sys.argv[2]))
