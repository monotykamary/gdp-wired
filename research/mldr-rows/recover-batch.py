"""Read-only recovery of an already registered supercomputer batch.

Uses the official client's long-poll/log endpoints. Never submit, close,
cancel, change policy, or run a proof. One bounded observer per batch.
"""
import io
import json
import pathlib
import sys
import tarfile
import time
from supercomputer.scheduler import Client

batch, directory, expected_text, seconds = sys.argv[1:]
expected = int(expected_text)
root = pathlib.Path(directory)
root.mkdir(parents=True, exist_ok=True)
client = Client()
deadline = time.monotonic() + float(seconds)
rows = {}
since = 0
while time.monotonic() < deadline:
    reply = client.req('/poll', {'batch': batch, 'since': since, 'wait': min(45, max(0, deadline - time.monotonic()))}, timeout=65)
    if reply.get('err'):
        raise RuntimeError(reply['err'])
    for row in reply.get('rows', []):
        since += 1
        name = row['name']
        if pathlib.PurePath(name).name != name:
            raise RuntimeError('unsafe result name')
        if name in rows and rows[name] != row:
            raise RuntimeError('conflicting duplicate result')
        rows[name] = row
        (root / 'recovered-rows.json').write_text(json.dumps(list(rows.values()), indent=2) + '\n')
        print(json.dumps({'batch': batch, 'name': name, 'code': row.get('code'), 'seconds': row.get('seconds'), 'keys': list(row)}), flush=True)
    if reply.get('done'):
        if len(rows) != expected:
            raise RuntimeError(f'incomplete batch: {len(rows)}/{expected}')
        vms = sorted({row['vm'] for row in rows.values() if row.get('vm')})
        archive = client.req('/logs', {'batch': batch, 'vms': vms}, timeout=600, raw=True)
        (root / 'recovered-logs.tar.gz').write_bytes(archive)
        by_run = {row.get('run_name', name): name for name, row in rows.items()}
        logs = {}
        with tarfile.open(fileobj=io.BytesIO(archive), mode='r:gz') as tf:
            for item in tf.getmembers():
                if not item.isfile() or '/' not in item.name:
                    continue
                run, stream = item.name.rsplit('/', 1)
                name = by_run.get(run)
                if name is not None and stream in ('out', 'err'):
                    logs.setdefault(name, {})[stream] = tf.extractfile(item).read().decode('utf-8', 'replace')
        for name, streams in logs.items():
            (root / (name + '.log')).write_text(streams.get('out', '') + '\n--- stderr ---\n' + streams.get('err', ''))
        (root / 'summary.tsv').write_text('name\texit\tseconds\twhere\n' + ''.join(f"{name}\t{row.get('code')}\t{row.get('seconds')}\t{row.get('vm')}\n" for name, row in rows.items()))
        receipt = {'batch': batch, 'expected': expected, 'rows': len(rows), 'logs': len(logs), 'complete': len(logs) == expected, 'resubmitted': False}
        (root / 'recovery.json').write_text(json.dumps(receipt, indent=2) + '\n')
        print(json.dumps(receipt), flush=True)
        if len(logs) != expected:
            raise RuntimeError('missing recovered logs')
        break
else:
    print(json.dumps({'batch': batch, 'observerTimedOut': True, 'rows': len(rows), 'expected': expected, 'remoteWorkCancelled': False}), flush=True)
    sys.exit(2)
