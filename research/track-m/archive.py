"""Recover only the MLDR research translation and Step 0 report; verify the archive hash."""
import hashlib, os, pathlib, tarfile, urllib.request, urllib.parse, http.cookiejar
from concurrent.futures import ThreadPoolExecutor
URL = os.environ['STORE_URL'].strip()
def url(path):
    u = urllib.parse.urlparse(URL)
    return urllib.parse.urlunparse(u._replace(path=u.path.rstrip('/') + '/' + path))
NAME = 'gdp-wired-dbae-astra.tgz'
SIZE = 564226317
SHA = 'f9cc6b4b98e70c6c7d7f799e56086295f89e3655c2e89e8e195eda3c1f993556'
p = pathlib.Path('/tmp') / NAME
# Range requests avoid the boat frontend's response cap.
jar = http.cookiejar.CookieJar()
opener = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(jar))
with opener.open(url('manifest.json'), timeout=60) as r:
    r.read()
with p.open('wb') as f:
    f.truncate(SIZE)
def get(a):
    end = min(SIZE, a + 4 * 1024 * 1024)
    with p.open('r+b') as f:
        pos = a
        for attempt in range(8):
            try:
                req = urllib.request.Request(url(NAME), headers={'Range': f'bytes={pos}-{end - 1}'})
                with opener.open(req, timeout=120) as r:
                    f.seek(pos)
                    while pos < end:
                        b = r.read(min(65536, end - pos))
                        if not b: break
                        f.write(b)
                        pos += len(b)
                if pos == end: return
            except Exception:
                pass
        raise RuntimeError(f'range {a}:{end} incomplete')
with ThreadPoolExecutor(8) as ex:
    list(ex.map(get, range(0, SIZE, 4 * 1024 * 1024)))
assert hashlib.file_digest(p.open('rb'), 'sha256').hexdigest() == SHA
print('ARCHIVE SHA256', SHA)
with tarfile.open(p) as tf:
    members = [m for m in tf.getmembers() if m.isfile() and not pathlib.PurePosixPath(m.name).name.startswith('._')]
    for suffix in ['research/protocols/ground-truth/published.ts', 'runs/REPORT.md']:
        matches = sorted([m for m in members if m.name.endswith(suffix)], key=lambda m: len(m.name))
        if not matches:
            print('MISSING', suffix)
            continue
        member = matches[0]
        text = tf.extractfile(member).read().decode()
        print('\nFILE', member.name)
        if member.name.endswith('REPORT.md'):
            start = text.find('Step 0')
            print(text[max(0, start - 300):start + 22000])
        else:
            print(text)
    print('REPORT PATHS', [m.name for m in members if 'REPORT' in m.name][:25])
