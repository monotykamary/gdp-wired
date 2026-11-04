"""Read only the two manifest-pinned lane archives on boat; never extract paths."""
import hashlib, http.cookiejar, json, os, re, tarfile, tempfile, urllib.request, urllib.parse
from pathlib import Path
manifest = json.loads(Path('research/egraph/historical/archive-meta/store-manifest.json').read_text())
u = urllib.parse.urlparse(os.environ['ASTRA_STORE_URL'])
opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(http.cookiejar.CookieJar()))
for lane in ['gdp-wired-laneQ3', 'gdp-wired-laneRL']:
    name = lane + '.tgz'
    url = urllib.parse.urlunparse(u._replace(path=u.path.rstrip('/') + '/' + name))
    with tempfile.TemporaryFile() as f:
        h = hashlib.sha256(); size = 0
        for attempt in range(8):
            if size == manifest[name][0]: break
            req = urllib.request.Request(url, headers={'Range': f'bytes={size}-{manifest[name][0]-1}'})
            with opener.open(req, timeout=120) as r:
                while chunk := r.read(1024 * 1024):
                    f.write(chunk); h.update(chunk); size += len(chunk)
        assert [size, h.hexdigest()] == manifest[name], (lane, size, h.hexdigest())
        print('ARCHIVE', name, size, h.hexdigest(), flush=True)
        f.seek(0)
        with tarfile.open(fileobj=f, mode='r:gz') as t:
            members = t.getmembers()
            import base64, gzip
            selected = [m for m in members if m.isfile() and '/._' not in m.name and not m.name.startswith('._') and ((m.name.startswith('runs/laneRL/tip-next/') and re.search(r'local-laws|snoc|depth2|manifest', m.name)) or m.name.startswith('core/fixtures/published-ground/'))]
            print('NARROW_INDEX', lane, json.dumps([(m.name, m.size) for m in selected]), flush=True)
            wanted = ['NEXT.md', 'research/frontier2/tasks/tip/prod/lemma_09.smt2', 'research/frontier2/tasks/tip/prod/lemma_09.broken.smt2', 'runs/q4-baseline-jobs.json', 'runs/q4-tools/replay-instantiation.ts', 'runs/REPORT-q3s.md']
            for m in members:
                specific = lane == 'gdp-wired-laneRL' and m.name.startswith('runs/laneRL/tip-next/') and (re.search(r'local-laws-(snoc|depth2|context|constructor|special)', m.name) is not None) and m.name.endswith(('.ts','.json','.log','.tsv')) and '/._' not in m.name
                if m.isfile() and (m.name in wanted or specific) and m.size < 200000:
                    data = t.extractfile(m).read()
                    print('ARTIFACT', json.dumps({'name': lane + '/' + m.name, 'sha256': hashlib.sha256(data).hexdigest(), 'gzipBase64': base64.b64encode(gzip.compress(data,mtime=0)).decode()}), flush=True)
