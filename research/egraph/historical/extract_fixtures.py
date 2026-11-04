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
            suffixes = ['research/frontier2/tasks/tip/prod/lemma_09.smt2', 'research/frontier2/tasks/tip/prod/lemma_09.broken.smt2'] if lane.endswith('RL') else ['core/fixtures/published-ground/paxos-P5-19.json', 'core/fixtures/published-ground/README.md']
            for suffix in suffixes:
                found = sorted([m for m in members if m.isfile() and m.name.endswith(suffix)], key=lambda m: (len(m.name), m.name))
                print('FIXTURE_CANDIDATES', lane, suffix, json.dumps([(m.name,m.size) for m in found]), flush=True)
                if not found: continue
                m = found[0]
                data = t.extractfile(m).read()
                print('ARTIFACT', json.dumps({'name': lane + '/' + suffix, 'sourceMember':m.name, 'sha256':hashlib.sha256(data).hexdigest(), 'gzipBase64':base64.b64encode(gzip.compress(data,mtime=0)).decode()}), flush=True)
