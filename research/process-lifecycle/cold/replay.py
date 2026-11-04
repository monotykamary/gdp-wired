"""Replay a fixed integer-call grammar on the exact pinned pure source. No eval."""
import hashlib
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'manifest.json').read_text())
file = 'research/process-lifecycle/broken.py'
source = root / 'source' / file
negative = root / 'negative.json'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
expected = {f['path']: f['sha256'] for f in manifest['files']}
source_before, negative_before = sha(source), sha(negative)
assert source_before == expected['source/' + file]
assert negative_before == expected['negative.json']
rules = json.loads(negative.read_text())['rules']
assert len(rules) == 1 and rules[0]['file'] == file and rules[0]['entry'] == 'BrokenDrain'
laws = rules[0]['laws']
assert len(laws) == 1
law = laws[0]
assert law['name'] == 'reaped has no in-flight signal'
assert law['expr'] == 'phase != 2 or inflight == 0' and law['where'] == 'broken.py:5'
assert law['verdict'] == 'broken'
calls = law['run']
assert isinstance(calls, list) and len(calls) == 4
pattern = re.compile(r'step\(action=(-?(?:0|[1-9][0-9]*))\)')
actions = []
for call in calls:
    assert isinstance(call, str)
    match = pattern.fullmatch(call)
    assert match is not None, 'not the fixed integer-call grammar'
    actions.append(int(match.group(1)))
assert actions == [0, -1, 1, 2]
sys.dont_write_bytecode = True
sys.path.insert(0, str(source.parent))
import broken
assert Path(broken.__file__).resolve() == source.resolve()
model = broken.BrokenDrain()
states = [{'step': 0, 'call': None, 'action': None, 'phase': model.phase, 'inflight': model.inflight}]
for i, (call, action) in enumerate(zip(calls, actions), 1):
    model.step(action)
    states.append({'step': i, 'call': call, 'action': action, 'phase': model.phase, 'inflight': model.inflight})
assert [(s['phase'], s['inflight']) for s in states] == [(0, 0), (0, 1), (0, 1), (1, 1), (2, 1)]
assert model.phase == 2 and model.inflight == 1
source_after, negative_after = sha(source), sha(negative)
assert source_before == source_after and negative_before == negative_after
print(json.dumps({'format': 'astra-exact-source-replay/1', 'accepted': True,
    'sourceFile': file, 'entry': 'BrokenDrain', 'actions': actions, 'calls': calls,
    'states': states, 'violation': 'phase == 2 and inflight == 1',
    'sourceBeforeSha256': source_before, 'sourceAfterSha256': source_after,
    'negativeBeforeSha256': negative_before, 'negativeAfterSha256': negative_after,
    'usedEval': False, 'actualProcessesOrSignalsInModel': False}), flush=True)
