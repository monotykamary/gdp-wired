"""Decode audit envelopes already returned by boat; no checking is executed locally."""
import base64, gzip, json, pathlib, sys
src=pathlib.Path(sys.argv[1]); out=pathlib.Path(sys.argv[2]); out.mkdir(parents=True,exist_ok=True)
rows=[]
for log in sorted(src.glob('*.log')):
    for line in log.read_text(errors='replace').splitlines():
        if line.startswith('RESULT '): rows.append(json.loads(line[7:]))
        if line.startswith('EVIDENCE_GZIP_BASE64 '):
            blob=json.loads(gzip.decompress(base64.b64decode(line.split(' ',1)[1])))
            target=out/log.stem; target.mkdir(exist_ok=True)
            for name,b64 in blob.items():
                p=target/name; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(base64.b64decode(b64))
(out/'results.json').write_text(json.dumps(rows,indent=2))
for r in rows:
    t=r.get('tlc',{}); p=r.get('port',{}).get('result') or {}; b=r.get('broken',{}).get('result') or {}
    print(r['id'], 'TLC',t.get('states'),t.get('edges'),t.get('complete'), 'port',p.get('states'),p.get('edges'),p.get('done'), 'bad',p.get('bad'), 'broken',b.get('bad'),b.get('done'),r.get('error','').splitlines()[-1:])
