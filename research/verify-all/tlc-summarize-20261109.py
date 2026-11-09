"""Format returned receipts only (no local model execution). Last directory wins per ID."""
import json, pathlib, sys
out=pathlib.Path('research/verify-all')
attempts=[]; latest={}
for dirname in sys.argv[1:]:
    for p in sorted(pathlib.Path(dirname).glob('tlc-*/result.json')):
        r=json.loads(p.read_text()); r['evidence_file']=str(p); attempts.append(r); latest[r['id']]=r
receipts=pathlib.Path('runs/verify-all/tlc-evidence-20261109.json')
receipts.parent.mkdir(parents=True,exist_ok=True)
receipts.write_text(json.dumps(attempts,indent=2)+'\n')
def fmt(v): return '—' if v is None else str(v).lower() if isinstance(v,bool) else str(v)
lines=['# Returned TLC/port receipts','','Counts are distinct projected states and distinct directed non-self edges. `done` is the unchanged port harness\'s flag; TLC complete is parsed independently. Broken `done=true` means the harness stopped after finding bad states, NOT exhaustive exploration.','', '| ID | TLC states | TLC edges | TLC complete / exit | port states | port edges | port done / exit | port bad | broken bad / done / exit |','|---|---:|---:|---|---:|---:|---|---:|---|']
for id,r in sorted(latest.items()):
    t=r.get('tlc',{}); p=r.get('port',{}); b=r.get('broken',{}); pr=p.get('result') or {}; br=b.get('result') or {}
    vals=[id,t.get('states'),t.get('edges'),f"{fmt(t.get('complete'))} / {fmt(t.get('exit'))}",pr.get('states'),pr.get('edges'),f"{fmt(pr.get('done'))} / {fmt(p.get('exit'))}",pr.get('bad'),f"{fmt(br.get('bad'))} / {fmt(br.get('done'))} / {fmt(b.get('exit'))}"]
    lines.append('| '+' | '.join(map(fmt,vals))+' |')
lines+=['','## All attempts (including failures)','','| ID | attempt evidence | ms budget | TLC state / edge / complete | port state / edge / done / exit | broken bad / done | wrapper error |','|---|---|---:|---|---|---|---|']
for r in attempts:
    t=r.get('tlc',{}); p=r.get('port',{}); b=r.get('broken',{}); pr=p.get('result') or {}; br=b.get('result') or {}
    lines.append('| '+' | '.join([r['id'],r['evidence_file'],str(r['ms']),'/'.join(fmt(t.get(k)) for k in ['states','edges','complete']),'/'.join(fmt(v) for v in [pr.get('states'),pr.get('edges'),pr.get('done'),p.get('exit')]),'/'.join(fmt(br.get(k)) for k in ['bad','done']),r.get('error','').splitlines()[-1].replace('|','/') if r.get('error') else 'none'])+' |')
lines+=['','## Effective source and configuration hashes','','See `runs/verify-all/tlc-evidence-20261109.json` for original source, graph, repo source hashes, all commands/cwd, timings and receipts.','', '| ID | module | effective TLA SHA-256 | config SHA-256 |','|---|---|---|---|']
for id,r in sorted(latest.items()):
    lines.append('| '+' | '.join([id,(r.get('meta') or {}).get('module','—'),r.get('used_spec_sha256','—'),r.get('cfg_sha256','—')])+' |')
(out/'tlc-results-20261109.md').write_text('\n'.join(lines)+'\n')
print('attempts',len(attempts),'IDs',len(latest))
print('\n'.join(lines[:35]))
