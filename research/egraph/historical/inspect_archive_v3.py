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
            selected = [m for m in members if m.isfile() and '/._' not in m.name and not m.name.startswith('._') and ('/trees/' not in m.name and '/vendor/' not in m.name and not m.name.startswith('runs/bar/')) and (m.name == 'NEXT.md' or re.search(r'(q4-(pause|tools|baseline|replay|p3)|tip|lemma|reverse)', m.name))]
            print('INDEX', lane, json.dumps([(m.name, m.size) for m in selected[:220]]), flush=True)
            for m in members:
                if m.isfile() and (m.name == 'NEXT.md' or 'q4-pause-checkpoint/README.md' in m.name):
                    data = t.extractfile(m).read()
                    print('FILE', m.name, hashlib.sha256(data).hexdigest(), flush=True)
                    print(data.decode(), flush=True)
