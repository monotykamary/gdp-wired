// Exercise the production pack function without importing Modal or constructing its image.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
const ready = (() => { try { execFileSync('python3', ['--version'], {stdio: 'ignore'}); execFileSync('zstd', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = ready ? test : test.skip
const prelude = String.raw`import ast, io, json, os, pathlib, re, subprocess, sys, tarfile, tempfile
scratch = tempfile.TemporaryDirectory(prefix='gdp-pack-test-')
source = pathlib.Path(sys.argv[1]).read_text()
node = next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == 'pack')
def setup(name='repo'):
    root = pathlib.Path(scratch.name) / name
    (root / 'goals').mkdir(parents=True)
    (root / 'research/query').mkdir(parents=True)
    space = {'json': json, 'pathlib': pathlib, 'os': os, 'GOALS': root / 'goals', 'GDP': root, 'GOAL': re.compile(r"(?<![\w./-])/goals/([^\s'\"]+)")}
    exec(compile(ast.Module(body=[node], type_ignores=[]), 'actual-pack-function', 'exec'), space)
    return root, space['pack']
def jobs(root, names):
    path = root / 'jobs.json'
    path.write_text(json.dumps([{'cmd': 'run /goals/' + name} for name in names]))
    return str(path)
def put(root, name, content=b'original goal bytes\n'):
    path = root / 'goals' / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(content)
    return path
`
const run = (body: string) => JSON.parse(execFileSync('python3', ['-c', prelude + '\n' + body, new URL('./modal_query.py', import.meta.url).pathname], {encoding: 'utf8', maxBuffer: 4 << 20}))

t('each packed hardlink is a regular, independently extractable goal', () => {
  expect(run(String.raw`root, pack = setup()
a = put(root, 'a/goal.json')
b = root / 'goals/b/goal.json'; b.parent.mkdir()
os.link(a, b)
archive = root / pack(jobs(root, ['a/goal.json', 'b/goal.json']))
raw = subprocess.check_output(['zstd', '-q', '-d', '-c', str(archive)])
with tarfile.open(fileobj=io.BytesIO(raw)) as tf:
    regular = all(m.isfile() for m in tf.getmembers())
codes, matches = [], []
for name in ('a', 'b'):
    out = root / ('out-' + name); out.mkdir()
    p = subprocess.run(['tar', '--zstd', '-xf', str(archive), '-C', str(out), 'goals/' + name + '/goal.json'], capture_output=True)
    codes.append(p.returncode)
    target = out / 'goals' / name / 'goal.json'
    matches.append(target.exists() and target.read_bytes() == a.read_bytes())
print(json.dumps({'regular': regular, 'codes': codes, 'matches': matches}))`)).toEqual({regular: true, codes: [0, 0], matches: [true, true]})
})

t('a symlinked goal is packed by value, not as an unresolved link', () => {
  expect(run(String.raw`root, pack = setup()
a = put(root, 'original.json')
b = root / 'goals/alias.json'; b.symlink_to('original.json')
archive = root / pack(jobs(root, ['alias.json']))
out = root / 'out'; out.mkdir()
p = subprocess.run(['tar', '--zstd', '-xf', str(archive), '-C', str(out), 'goals/alias.json'], capture_output=True)
target = out / 'goals/alias.json'
print(json.dumps({'code': p.returncode, 'regular': target.is_file() and not target.is_symlink(), 'matches': target.exists() and target.read_bytes() == a.read_bytes()}))`)).toEqual({code: 0, regular: true, matches: true})
})

t('goal packing handles a repository root containing spaces', () => {
  expect(run(String.raw`root, pack = setup('space root')
a = put(root, 'a.json')
archive = root / pack(jobs(root, ['a.json']))
raw = subprocess.check_output(['zstd', '-q', '-d', '-c', str(archive)])
with tarfile.open(fileobj=io.BytesIO(raw)) as tf:
    same = tf.extractfile('goals/a.json').read() == a.read_bytes()
print(json.dumps(same))`)).toBe(true)
})

t('an empty goal selection creates no archive', () => {
  expect(run(String.raw`root, pack = setup()
result = pack(jobs(root, []))
print(json.dumps({'result': result, 'files': list((root / 'research/query').iterdir())}))`)).toEqual({result: '', files: []})
})

t('a missing goal fails packing without leaving an incomplete archive', () => {
  expect(run(String.raw`root, pack = setup()
failed = False
try:
    pack(jobs(root, ['missing.json']))
except Exception:
    failed = True
print(json.dumps({'failed': failed, 'files': [p.name for p in (root / 'research/query').iterdir()]}))`)).toEqual({failed: true, files: []})
})

t('failed packing preserves a previously complete archive atomically', () => {
  expect(run(String.raw`root, pack = setup()
target = root / 'research/query' / ('.goals-' + str(os.getpid()) + '.tar.zst')
target.write_bytes(b'previous complete archive')
failed = False
try:
    pack(jobs(root, ['missing.json']))
except Exception:
    failed = True
print(json.dumps({'failed': failed, 'preserved': target.read_bytes() == b'previous complete archive', 'files': len(list(target.parent.iterdir()))}))`)).toEqual({failed: true, preserved: true, files: 1})
})

t('a compressor failure leaves no archive or temporary output', () => {
  expect(run(String.raw`root, pack = setup()
put(root, 'a.json')
bin = root / 'bin'; bin.mkdir()
fake = bin / 'zstd'; fake.write_text('#!/bin/sh\nexit 7\n'); fake.chmod(0o755)
os.environ['PATH'] = str(bin) + os.pathsep + os.environ['PATH']
failed = False
try:
    pack(jobs(root, ['a.json']))
except Exception:
    failed = True
print(json.dumps({'failed': failed, 'files': [p.name for p in (root / 'research/query').iterdir()]}))`)).toEqual({failed: true, files: []})
})
