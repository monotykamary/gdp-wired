"""Pure, conditional validation of documented deletion responses; no I/O.

The caller supplies an already authenticated account/request context and a
complete framed HTTP body. Neither assertion is proved by this parser.
OpenAPI SHA256: 9f2abcf0735ba6230fba1b40ac9a11fe9022348997152821f3b99a1f7c2421fc.
"""
from dataclasses import dataclass
from datetime import datetime
import json
import math
import re

MAX_BODY_BYTES = 65536
MAX_DEPTH = 16
MAX_NODES = 4096
MAX_NUMBER_CHARS = 128

KINDS = frozenset(('sandbox', 'snapshot'))
REASONS = frozenset(('explicit', 'zdr', 'account'))
STATUSES = frozenset(('pending', 'processing', 'blocked', 'completed'))
STAGES = frozenset(('removing', 'waiting_for_uploads', 'retrying', 'completed'))
# These are the three literals actually documented by DeletionOperationResponse.
ENVELOPES = frozenset(('deletion.operation', 'sandbox.deleting', 'snapshot.deleting'))
_OPERATION = re.compile(r'bdop_[a-f0-9]{32}\Z')
_SANDBOX = re.compile(r'bx_[23456789abcdefghjkmnpqrstuvwxyz]{8}\Z')
_SNAPSHOT = re.compile(r'[a-fA-F0-9]{8}(?:-[a-fA-F0-9]{4}){3}-[a-fA-F0-9]{12}\Z')
_TIME = re.compile(r'[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}'
                   r'(?:\.[0-9]{1,6})?(?:Z|[+-][0-9]{2}:[0-9]{2})\Z')


class DecodeError(ValueError):
    """A fixed diagnostic code only; never includes body, headers or IDs."""


class _Rejected(ValueError):
    pass


@dataclass(frozen=True)
class RequestContext:
    target_id: str
    kind: str
    reason: str = 'explicit'
    authenticated_account_bound: bool = False
    response_complete: bool = False


@dataclass(frozen=True)
class DeletionResponse:
    operation_id: str
    target_id: str
    kind: str
    reason: str
    status: str
    attempt_count: int
    requested_at: str
    completed_at: str | None
    stage: str | None
    expected_by: str | None
    phase: str
    terminal: bool
    account_binding: str = 'conditional-on-supplied-context'
    authentication_proven: bool = False
    http_framing_proven: bool = False
    native_evidence: bool = False
    referenced_data_may_remain: bool = True
    proves_global_erasure: bool = False


def _fail(code):
    raise DecodeError(code)


def _member(value, choices):
    return type(value) is str and value in choices


def _matches(value, pattern):
    return type(value) is str and pattern.fullmatch(value) is not None


def _context(context):
    if type(context) is not RequestContext:
        _fail('invalid-context')
    if context.authenticated_account_bound is not True:
        _fail('unbound-authenticated-context')
    if context.response_complete is not True:
        _fail('incomplete-http-message')
    if not _member(context.kind, KINDS) or not _member(context.reason, REASONS):
        _fail('invalid-context')
    pattern = _SANDBOX if context.kind == 'sandbox' else _SNAPSHOT
    if not _matches(context.target_id, pattern):
        _fail('invalid-context')


def _pairs(pairs):
    out = {}
    for key, value in pairs:
        if key in out:
            raise _Rejected('duplicate-key')
        out[key] = value
    return out


def _integer(token):
    if len(token) > MAX_NUMBER_CHARS:
        raise _Rejected('number-limit')
    return int(token)


def _float(token):
    if len(token) > MAX_NUMBER_CHARS:
        raise _Rejected('number-limit')
    value = float(token)
    if not math.isfinite(value):
        raise _Rejected('nonfinite-number')
    return value


def _constant(_token):
    raise _Rejected('nonfinite-number')


def _depth(text):
    depth, quoted, escaped = 0, False, False
    for char in text:
        if quoted:
            if escaped:
                escaped = False
            elif char == '\\':
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char in '[{':
            depth += 1
            if depth > MAX_DEPTH:
                _fail('depth-limit')
        elif char in ']}':
            depth -= 1


def _tree(value):
    """Bound all JSON nodes and reject escaped unpaired Unicode surrogates."""
    pending, count = [value], 0
    while pending:
        item = pending.pop()
        count += 1
        if count > MAX_NODES:
            _fail('node-limit')
        if type(item) is dict:
            pending.extend(item.keys())
            pending.extend(item.values())
        elif type(item) is list:
            pending.extend(item)
        elif type(item) is str:
            invalid = False
            try:
                item.encode('utf-8', 'strict')
            except UnicodeError:
                invalid = True
            if invalid:
                _fail('invalid-unicode')


def _body(body):
    if type(body) is not bytes:
        _fail('body-must-be-bytes')
    if not body or len(body) > MAX_BODY_BYTES:
        _fail('body-size')
    text, error = None, None
    try:
        text = body.decode('utf-8', 'strict')
    except UnicodeError:
        error = 'invalid-utf8'
    # Raise outside the exception handler: even __context__ must not retain
    # UnicodeDecodeError/JSONDecodeError objects containing the raw body.
    if error:
        _fail(error)
    _depth(text)
    value = None
    try:
        value = json.loads(text, object_pairs_hook=_pairs, parse_int=_integer,
                           parse_float=_float, parse_constant=_constant)
    except _Rejected as exc:
        error = str(exc)  # only fixed codes produced above
    except (ValueError, RecursionError, OverflowError):
        error = 'invalid-json'
    if error:
        _fail(error)
    _tree(value)
    if type(value) is not dict:
        _fail('invalid-envelope')
    return value


def _time(value):
    # A deliberately bounded RFC3339 profile: numeric offset or Z, up to six
    # fraction digits, no leap-second normalization or timezone database I/O.
    if not _matches(value, _TIME):
        _fail('invalid-timestamp')
    parsed, error = None, False
    try:
        parsed = datetime.fromisoformat(value[:-1] + '+00:00' if value.endswith('Z') else value)
    except ValueError:
        error = True
    if error:
        _fail('invalid-timestamp')
    return parsed


def _decode(status, body, context, phase, expected_operation_id):
    _context(context)
    expected_status = 202 if phase == 'acceptance' else 200
    if type(status) is not int or status != expected_status:
        _fail('unexpected-http-status')
    if phase == 'observation' and not _matches(expected_operation_id, _OPERATION):
        _fail('invalid-expected-operation')
    envelope = _body(body)
    if envelope.get('ok') is not True or not _member(envelope.get('type'), ENVELOPES):
        _fail('invalid-envelope')
    operation = envelope.get('operation')
    required = ('id', 'kind', 'targetId', 'reason', 'status', 'attemptCount',
                'requestedAt', 'completedAt')
    if type(operation) is not dict or any(key not in operation for key in required):
        _fail('invalid-operation')
    if not _matches(operation['id'], _OPERATION):
        _fail('invalid-operation-id')
    if phase == 'observation' and operation['id'] != expected_operation_id:
        _fail('operation-mismatch')
    if (operation['kind'] != context.kind or operation['targetId'] != context.target_id
            or operation['reason'] != context.reason):
        _fail('request-context-mismatch')
    if not _member(operation['status'], STATUSES):
        _fail('invalid-operation-status')
    attempts = operation['attemptCount']
    if type(attempts) is not int or attempts < 0:
        _fail('invalid-attempt-count')
    stage = operation.get('stage')
    if 'stage' in operation and not _member(stage, STAGES):
        _fail('invalid-operation-stage')
    requested = _time(operation['requestedAt'])
    completed = operation['completedAt']
    if operation['status'] == 'completed':
        if completed is None or _time(completed) < requested:
            _fail('inconsistent-completion')
        if stage is not None and stage != 'completed':
            _fail('inconsistent-completion')
    elif completed is not None or stage == 'completed':
        _fail('inconsistent-completion')
    expected_by = operation.get('expectedBy')
    if expected_by is not None:
        _time(expected_by)
    return DeletionResponse(
        operation_id=operation['id'], target_id=context.target_id,
        kind=context.kind, reason=context.reason, status=operation['status'],
        attempt_count=attempts, requested_at=operation['requestedAt'],
        completed_at=completed, stage=stage, expected_by=expected_by,
        phase=phase, terminal=phase == 'observation' and operation['status'] == 'completed')


def decode_acceptance(status: int, body: bytes, context: RequestContext) -> DeletionResponse:
    """Decode a 202 DELETE acceptance; never claim terminal completion here."""
    return _decode(status, body, context, 'acceptance', None)


def decode_operation_response(status: int, body: bytes, context: RequestContext,
                              expected_operation_id: str) -> DeletionResponse:
    """Decode a 200 exact-operation response, conditional on supplied context."""
    return _decode(status, body, context, 'observation', expected_operation_id)
