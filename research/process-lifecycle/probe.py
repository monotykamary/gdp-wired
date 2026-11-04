"""Finite pure-state cross-check and concrete broken trace. No OS lifecycle calls."""
import itertools
import json
from model import Lifecycle
from broken import BrokenDrain

transitions = 0
for actions in itertools.product(range(5), repeat=6):
    state = Lifecycle()
    for action in actions:
        phase, owner, inflight, admissions = state.phase, state.owner, state.inflight, state.admissions
        state.step(action)
        assert 0 <= state.phase <= 3 and state.inflight >= 0
        if phase in (1, 2, 3) or not owner:
            assert state.admissions == admissions
        if state.phase == 2:
            assert state.inflight == 0
            if phase != 2:
                assert inflight == 0
        if phase != 0:
            assert state.phase != 0
        if not owner:
            assert not state.owner
        assert state.owner or state.phase == 3
        transitions += 1
bug = BrokenDrain()
trace = []
for action in (0, 1, 2):
    bug.step(action)
    trace.append({'action': action, 'phase': bug.phase, 'inflight': bug.inflight})
assert bug.phase == 2 and bug.inflight == 1
print('PURE_PROBE ' + json.dumps({'sequences': 5**6, 'transitions': transitions,
    'passed': True, 'brokenControlReplayed': trace, 'actualProcessesOrSignals': False}))
