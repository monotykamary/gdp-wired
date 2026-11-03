"""Local-copy benchmark support. No services, network calls, or upstream writes."""
import ast
import copy
import hashlib
import inspect
import json
import runpy
import sys
from pathlib import Path


def read(path):
    return Path(path).read_bytes().decode('utf-8')


def inventory(source, entry):
    cls = next(n for n in ast.parse(source).body if isinstance(n, ast.ClassDef) and n.name == entry)
    methods, properties = [], []
    for n in cls.body:
        if not isinstance(n, ast.FunctionDef) or n.name.startswith('_'):
            continue
        if any(isinstance(d, ast.Name) and d.id == 'property' for d in n.decorator_list):
            properties.append(n.name)
        else:
            methods.append(n.name)
    return cls, methods, properties


def annotate(source, case):
    cls, methods, properties = inventory(source, case['entry'])
    if methods != case['methods'] or properties != case['properties']:
        raise ValueError('the configured surface omits or invents a public callable/property')
    lines = source.splitlines(keepends=True)
    additions = []
    for policy in case['policies']:
        node = next(n for n in cls.body if isinstance(n, ast.FunctionDef) and n.name == policy['method']) if policy.get('method') else cls
        indent = lines[node.lineno - 1][:len(lines[node.lineno - 1]) - len(lines[node.lineno - 1].lstrip())]
        additions.append((node.lineno - 1, indent + '# gdp: law ' + policy['name'] + ': ' + policy['expr'] + '\n'))
    for index, comment in sorted(additions, reverse=True):
        lines.insert(index, comment)
    annotated = ''.join(lines)
    if ast.dump(ast.parse(source)) != ast.dump(ast.parse(annotated)):
        raise ValueError('policy annotation changed executable syntax')
    return annotated


def mutate(source, entry):
    cls, _, _ = inventory(source, entry)
    raw = source.encode('utf-8')
    lines = raw.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    out = []
    for method in cls.body:
        if not isinstance(method, ast.FunctionDef) or method.name.startswith('_') or method.decorator_list:
            continue
        for node in ast.walk(method):
            if not isinstance(node, ast.If) or node.orelse:
                continue
            denies = any(isinstance(n, ast.Raise) or isinstance(n, ast.Return) and isinstance(n.value, ast.Constant) and n.value.value is False for n in node.body)
            writes = any(isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Attribute) and isinstance(n.target.value, ast.Name) and n.target.value.id == 'self' for n in node.body)
            if not denies and not writes:
                continue
            test = node.test
            start = offsets[test.lineno - 1] + test.col_offset
            end = offsets[test.end_lineno - 1] + test.end_col_offset
            before = raw[start:end].decode('utf-8')
            edits = [('remove-guard', 'False' if denies else 'True'), ('invert-guard', 'not (' + before + ')')]
            swapped = {ast.Lt: ast.LtE, ast.LtE: ast.Lt, ast.Gt: ast.GtE, ast.GtE: ast.Gt}
            if isinstance(test, ast.Compare) and len(test.ops) == 1 and type(test.ops[0]) in swapped:
                changed = copy.deepcopy(test)
                changed.ops[0] = swapped[type(test.ops[0])]()
                edits.append(('boundary', ast.unparse(changed)))
            for operator, after in edits:
                mutant = (raw[:start] + after.encode('utf-8') + raw[end:]).decode('utf-8')
                ast.parse(mutant)
                out.append(dict(id=f'{operator}-{start}', operator=operator, method=method.name, startByte=start, endByte=end, before=before, after=after, source=mutant))
    return out


class Constants(ast.NodeTransformer):
    def visit_Name(self, node):
        values = {'true': True, 'false': False, 'null': None, 'undefined': None}
        return ast.copy_location(ast.Constant(values[node.id]), node) if node.id in values else node


def call(line):
    text = 'constructor(' + line[10:] + ')' if line.startswith('made with ') else line
    node = ast.parse(text, mode='eval').body
    if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name) or node.args or any(k.arg is None for k in node.keywords):
        raise ValueError('unsupported source call')
    args = {k.arg: ast.literal_eval(Constants().visit(k.value)) for k in node.keywords}
    if len(args) != len(node.keywords):
        raise ValueError('duplicate source argument')
    return dict(method=node.func.id, args=args)


def snapshot(obj):
    # Opaque lock objects stay in the real object and are used by the real methods.
    # They are not replaced or simulated, and are not scalar policy state.
    return {k: v for k, v in vars(obj).items() if v is None or isinstance(v, (bool, int, str))}


def replay(request):
    path = Path(request['file']).resolve()
    sys.path.insert(0, str(path.parent))
    module = runpy.run_path(str(path))
    cls = module[request['entry']]
    calls = [call(line) for line in request['run']]
    params = calls.pop(0)['args'] if calls and calls[0]['method'] == 'constructor' else {}
    inspect.signature(cls).bind(**params)
    obj = cls(**params)
    initial, steps = snapshot(obj), []
    for event in calls:
        if event['method'].startswith('_'):
            raise ValueError('private/dunder call is not a public request')
        method = getattr(obj, event['method'])
        inspect.signature(method).bind(**event['args'])
        before = {**snapshot(obj), **event['args']}
        failed, result = False, None
        try:
            result = method(**event['args'])
        except Exception:
            failed = True
        if result is not None and not isinstance(result, (bool, int, str)):
            raise ValueError('non-scalar method result outside replay scope')
        steps.append(dict(call=event, before=before, after={**snapshot(obj), **event['args'], 'result': result, 'failed': failed}))
    return dict(ok=True, initial=initial, steps=steps, sourceSha256=hashlib.sha256(path.read_bytes()).hexdigest())


if __name__ == '__main__':
    request = json.loads(Path(sys.argv[1]).read_text())
    try:
        action = request['action']
        if action == 'prepare':
            source = read(request['file'])
            annotated = annotate(source, request['case'])
            result = dict(source=annotated, mutations=mutate(annotated, request['case']['entry']))
        elif action == 'mutate':
            result = mutate(request['source'], request['entry'])
        elif action == 'replay':
            result = replay(request)
        else:
            raise ValueError('unknown operation')
        print(json.dumps(result, ensure_ascii=False))
    except Exception as error:
        print(json.dumps(dict(ok=False, why=f'{type(error).__name__}: {error}')))
        sys.exit(1)
