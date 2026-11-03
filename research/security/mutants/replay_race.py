"""Owned synchronous cache/effect modules only; no database or third-party probing.
Replay a CLI schedule on the actual Python method under its stated isolation.
An atomic parent's replay serializes the same requests (the RC schedule is illegal there).
"""
import ast
import hashlib
import inspect
import json
import re
import runpy
import sys
import threading
from collections import Counter
from pathlib import Path


def replay(request):
    path = Path(request['file'])
    source = path.read_text()
    env = re.search(r'^# gdp: env (atomic|read committed)$', source, re.M)
    policy = re.fullmatch(r'at most one call between (\w+) and \1', request['expr'])
    if not env or not policy:
        raise ValueError('unsupported isolation or flow policy')
    effect_names = set()
    lines = source.splitlines()
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) and '# gdp: effect' in lines[node.lineno - 1]:
            effect_names.add(node.value.func.attr)
    if not effect_names:
        raise ValueError('no declared effect to observe')
    atomic = env[1] == 'atomic'
    calls, gates, threads, effects, errors, operations = {}, {}, {}, [], [], []
    completed_arguments = []
    local = threading.local()
    stores = {}

    class Adapter:
        def __init__(self, name):
            self.name = name
            self.data = stores.setdefault(name, {})

        def get(self, key):
            cid = local.cid
            if not atomic:
                g = gates[cid]
                if g['arrived'].is_set():
                    raise ValueError('more than one store read is outside replay subset')
                g['arrived'].set()
                if not g['read'].wait(5):
                    raise TimeoutError('read not scheduled')
            value = self.data.get(key)
            operations.append({'call': cid, 'get': self.name, 'key': key, 'value': value})
            if not atomic:
                g['read_done'].set()
                if not g['commit'].wait(5):
                    raise TimeoutError('commit not scheduled')
            return value

        def set(self, key, value):
            self.data[key] = value
            operations.append({'call': local.cid, 'set': self.name, 'key': key, 'value': value})

        def __getattr__(self, name):
            if name not in effect_names:
                raise ValueError('undeclared dependency call: ' + name)
            def effect(*args):
                effects.append({'call': local.cid, 'dependency': self.name, 'method': name, 'args': args})
            return effect

    cls = runpy.run_path(str(path))[request['entry']]
    params = inspect.signature(cls).parameters
    obj = cls(**{name: Adapter(name) for name in params})

    def execute(cid):
        local.cid = cid
        try:
            method, args = calls[cid]
            getattr(obj, method)(**args)
        except BaseException as error:
            errors.append(type(error).__name__ + ': ' + str(error))

    try:
        for line in request['run']:
            begin = re.fullmatch(r'call (\d+) begins (.*)', line)
            read = re.fullmatch(r'call (\d+) reads (.*)', line)
            commit = re.fullmatch(r'call (\d+) commits', line)
            if begin:
                cid = int(begin[1])
                call = ast.parse(begin[2], mode='eval').body
                if not isinstance(call, ast.Call) or not isinstance(call.func, ast.Name) or call.func.id != policy[1] or call.args or cid in calls:
                    raise ValueError('unsupported or duplicate call')
                args = {k.arg: ast.literal_eval(k.value) for k in call.keywords}
                signature = inspect.signature(getattr(obj, call.func.id))
                # The extractor can project away effect payloads irrelevant to the law. Complete
                # only primitive typed inputs, record them, and actually execute that completion.
                for name, parameter in signature.parameters.items():
                    if name in args:
                        continue
                    if parameter.default is not inspect.Parameter.empty:
                        value = parameter.default
                    elif parameter.annotation in (int, str, bool):
                        value = {int: 0, str: '', bool: False}[parameter.annotation]
                    else:
                        raise ValueError('untyped missing witness argument: ' + name)
                    args[name] = value
                    completed_arguments.append({'call': cid, 'name': name, 'value': value})
                signature.bind(**args)
                calls[cid] = (call.func.id, args)
                if atomic:
                    execute(cid)
                else:
                    gates[cid] = {k: threading.Event() for k in ('arrived', 'read', 'read_done', 'commit')}
                    threads[cid] = threading.Thread(target=execute, args=(cid,), daemon=True)
                    threads[cid].start()
                    if not gates[cid]['arrived'].wait(5):
                        raise TimeoutError('source did not reach its read')
            elif read:
                if not atomic:
                    g = gates[int(read[1])]
                    if g['read_done'].is_set():
                        raise ValueError('duplicate read')
                    g['read'].set()
                    if not g['read_done'].wait(5):
                        raise TimeoutError('source read did not complete')
            elif commit:
                if not atomic:
                    cid = int(commit[1])
                    if not gates[cid]['read_done'].is_set():
                        raise ValueError('commit before read')
                    gates[cid]['commit'].set()
                    threads[cid].join(5)
                    if threads[cid].is_alive():
                        raise TimeoutError('source commit did not complete')
            else:
                raise ValueError('unrecognized schedule line: ' + line)
        if len(calls) < 2 or errors or any(t.is_alive() for t in threads.values()):
            raise ValueError('incomplete source replay: ' + repr(errors))
        successful = {e['call'] for e in effects}
        counts = Counter(json.dumps(calls[cid], sort_keys=True) for cid in successful)
        return {'ok': True, 'broken': any(n > 1 for n in counts.values()), 'steps': operations,
                'effects': effects, 'calls': calls, 'completedArguments': completed_arguments, 'isolation': env[1], 'schedule': 'same CLI schedule' if not atomic else 'same requests serialized under atomic',
                'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    finally:
        for g in gates.values():
            g['read'].set()
            g['commit'].set()
        for t in threads.values():
            t.join(5)


if __name__ == '__main__':
    try:
        result = replay(json.loads(Path(sys.argv[1]).read_text()))
    except Exception as error:
        result = {'ok': False, 'broken': False, 'steps': [], 'why': type(error).__name__ + ': ' + str(error)}
    print(json.dumps(result))
