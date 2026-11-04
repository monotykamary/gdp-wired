"""Synthetic contract tests only; no filesystem, credentials or provider I/O."""
from dataclasses import FrozenInstanceError, replace
import copy
import json
import traceback
import unittest

from delete_response import (DecodeError, RequestContext, decode_acceptance,
    decode_operation_response, ENVELOPES, MAX_BODY_BYTES, MAX_DEPTH, MAX_NODES,
    MAX_NUMBER_CHARS)

OP = 'bdop_' + 'a' * 32
OTHER_OP = 'bdop_' + 'b' * 32
TARGET = 'bx_23456789'
OTHER_TARGET = 'bx_abcdefgh'
SNAPSHOT = '7417be09-d419-4ae0-b3fc-7f04a5a71ef1'
START = '2026-11-04T03:14:40.995Z'
END = '2026-11-04T03:14:44.945Z'
CONTEXT = RequestContext(TARGET, 'sandbox', authenticated_account_bound=True,
                         response_complete=True)


def document(status='pending', **changes):
    operation = {'id': OP, 'kind': 'sandbox', 'targetId': TARGET, 'reason': 'explicit',
                 'status': status, 'attemptCount': 1, 'requestedAt': START,
                 'completedAt': END if status == 'completed' else None}
    operation.update(changes)
    return {'ok': True, 'type': 'deletion.operation', 'operation': operation}


def body(doc=None):
    return json.dumps(document() if doc is None else doc, separators=(',', ':')).encode()


class DeleteResponseTests(unittest.TestCase):
    def decode(self, doc=None, *, context=CONTEXT, expected=OP, status=200):
        data = doc if type(doc) is bytes else body(doc)
        return decode_operation_response(status, data, context, expected)

    def refused(self, data, code=None, **kwargs):
        with self.assertRaises(DecodeError) as caught:
            self.decode(data, **kwargs)
        if code:
            self.assertEqual(str(caught.exception), code)
        self.assertIsNone(caught.exception.__cause__)
        self.assertIsNone(caught.exception.__context__)
        return caught.exception

    def test_acceptance_discovers_operation_but_is_not_terminal(self):
        result = decode_acceptance(202, body(), CONTEXT)
        self.assertEqual(result.operation_id, OP)
        self.assertEqual(result.phase, 'acceptance')
        self.assertFalse(result.terminal)

    def test_202_even_with_completed_operation_is_not_terminal(self):
        result = decode_acceptance(202, body(document('completed')), CONTEXT)
        self.assertEqual(result.status, 'completed')
        self.assertFalse(result.terminal)

    def test_completed_observation_is_conditional_not_physical_proof(self):
        result = self.decode(document('completed', stage='completed'))
        self.assertTrue(result.terminal)
        self.assertEqual(result.phase, 'observation')
        self.assertEqual(result.account_binding, 'conditional-on-supplied-context')
        self.assertFalse(result.authentication_proven)
        self.assertFalse(result.http_framing_proven)
        self.assertFalse(result.native_evidence)
        self.assertTrue(result.referenced_data_may_remain)
        self.assertFalse(result.proves_global_erasure)

    def test_pending_processing_blocked_are_not_completed(self):
        for status in ('pending', 'processing', 'blocked'):
            for stage in (None, 'removing', 'waiting_for_uploads', 'retrying'):
                with self.subTest(status=status, stage=stage):
                    doc = document(status)
                    if stage is not None:
                        doc['operation']['stage'] = stage
                    self.assertFalse(self.decode(doc).terminal)

    def test_optional_stage_and_expected_by(self):
        self.assertIsNone(self.decode().stage)
        self.assertIsNone(self.decode().expected_by)
        self.assertIsNone(self.decode(document(expectedBy=None)).expected_by)
        result = self.decode(document('blocked', stage='waiting_for_uploads', expectedBy=END))
        self.assertEqual(result.expected_by, END)
        self.assertFalse(result.terminal)
        self.assertTrue(self.decode(document('completed', expectedBy=END)).terminal)

    def test_optional_fields_do_not_invent_required_dependencies(self):
        self.assertFalse(self.decode(document(stage='waiting_for_uploads')).terminal)
        self.assertTrue(self.decode(document('completed')).terminal)

    def test_only_documented_envelope_literals(self):
        for envelope in ENVELOPES:
            with self.subTest(envelope=envelope):
                doc = document()
                doc['type'] = envelope
                self.assertEqual(self.decode(doc).operation_id, OP)
        for envelope in ('deletion.accepted', 'deletion.completed', 'sandbox.deleted', None, 1):
            doc = document()
            doc['type'] = envelope
            self.refused(doc, 'invalid-envelope')

    def test_required_success_envelope(self):
        for key in ('ok', 'type'):
            doc = document()
            del doc[key]
            self.refused(doc, 'invalid-envelope')
        for value in (False, 1, 'true', None, []):
            doc = document()
            doc['ok'] = value
            self.refused(doc, 'invalid-envelope')
        self.refused({'operation': document()['operation']}, 'invalid-envelope')

    def test_required_operation_fields(self):
        for key in document()['operation']:
            with self.subTest(key=key):
                doc = document()
                del doc['operation'][key]
                self.refused(doc, 'invalid-operation')
        for value in (None, [], True, 'operation'):
            doc = document()
            doc['operation'] = value
            self.refused(doc, 'invalid-operation')

    def test_exact_operation_correlation(self):
        self.refused(document(id=OTHER_OP), 'operation-mismatch')
        for value in ('', None, OTHER_OP.encode(), 'bdop_wrong', 'bdop_' + 'A' * 32):
            with self.subTest(expected=value):
                self.refused(document(), 'invalid-expected-operation', expected=value)

    def test_invalid_response_operation_id(self):
        for value in ('bdop_wrong', None, 1, 'bdop_' + 'A' * 32, OP + 'x'):
            self.refused(document(id=value), 'invalid-operation-id')

    def test_exact_target_kind_and_reason(self):
        for change in ({'targetId': OTHER_TARGET}, {'targetId': None}, {'kind': 'snapshot'},
                       {'kind': True}, {'reason': 'account'}, {'reason': 'zdr'}, {'reason': []}):
            with self.subTest(change=change):
                self.refused(document(**change), 'request-context-mismatch')

    def test_documented_snapshot_kind_and_expected_reason(self):
        context = replace(CONTEXT, target_id=SNAPSHOT, kind='snapshot')
        result = self.decode(document(kind='snapshot', targetId=SNAPSHOT), context=context)
        self.assertEqual(result.target_id, SNAPSHOT)
        for reason in ('explicit', 'account', 'zdr'):
            result = self.decode(document(reason=reason), context=replace(CONTEXT, reason=reason))
            self.assertEqual(result.reason, reason)

    def test_context_is_an_explicit_condition_not_response_claim(self):
        doc = document('completed')
        doc['account'] = 'invented-account'
        doc['authenticated'] = True
        doc['operation']['account'] = 'invented-account'
        for context in (replace(CONTEXT, authenticated_account_bound=False),
                        replace(CONTEXT, authenticated_account_bound=1)):
            self.refused(doc, 'unbound-authenticated-context', context=context)
        for context in (replace(CONTEXT, response_complete=False),
                        replace(CONTEXT, response_complete=1)):
            self.refused(doc, 'incomplete-http-message', context=context)
        self.assertFalse(self.decode(doc).authentication_proven)

    def test_invalid_context(self):
        for context in (None, {}, replace(CONTEXT, target_id='secret-invalid-target'),
                        replace(CONTEXT, kind='unknown'), replace(CONTEXT, reason='unknown'),
                        replace(CONTEXT, kind='snapshot', target_id=TARGET)):
            self.refused(document(), 'invalid-context', context=context)

    def test_exact_http_status(self):
        for status in (202, 204, 206, 301, 401, 403, 404, 409, 429, 500, True, 200.0, '200'):
            self.refused(document('completed'), 'unexpected-http-status', status=status)
        for status in (200, 204, 404, True, 202.0):
            with self.assertRaisesRegex(DecodeError, '^unexpected-http-status$'):
                decode_acceptance(status, body(), CONTEXT)

    def test_status_stage_and_count_schema(self):
        for status in ('deleted', 'complete', True, None, []):
            self.refused(document(status=status), 'invalid-operation-status')
        for stage in ('done', True, None, [], ''):
            self.refused(document(stage=stage), 'invalid-operation-stage')
        for count in (-1, 1.0, True, False, '1', None, []):
            self.refused(document(attemptCount=count), 'invalid-attempt-count')
        self.assertEqual(self.decode(document(attemptCount=0)).attempt_count, 0)
        self.assertEqual(self.decode(document(attemptCount=100)).attempt_count, 100)

    def test_terminal_consistency(self):
        self.refused(document('completed', completedAt=None), 'inconsistent-completion')
        self.refused(document('completed', completedAt='2026-11-04T03:00:00Z'), 'inconsistent-completion')
        for stage in ('removing', 'retrying', 'waiting_for_uploads'):
            self.refused(document('completed', stage=stage), 'inconsistent-completion')
        for status in ('pending', 'processing', 'blocked'):
            self.refused(document(status, completedAt=END), 'inconsistent-completion')
            self.refused(document(status, stage='completed'), 'inconsistent-completion')

    def test_timestamp_profile(self):
        for value in ('2026-13-04T03:14:40Z', '2026-02-30T03:14:40Z', '2026-11-04',
                      '2026-11-04T03:14:40', '2026-11-04T03:14:60Z',
                      '2026-11-04T03:14:40+99:00', '2026-11-04T03:14:40.1234567Z',
                      None, 1, [], 'credential-marker'):
            self.refused(document(requestedAt=value), 'invalid-timestamp')
            self.refused(document(expectedBy=value) if value is not None else document(expectedBy=1),
                         'invalid-timestamp')
        result = self.decode(document('completed', requestedAt='2026-11-04T04:14:40.000001+01:00',
                                      completedAt='2026-11-04T03:14:40.000002Z'))
        self.assertTrue(result.terminal)
        self.refused(document('completed', requestedAt='2026-11-04T04:14:40+01:00',
                              completedAt='2026-11-04T03:14:39Z'), 'inconsistent-completion')

    def test_body_type_and_size_limits(self):
        for data in ('{}', bytearray(body()), memoryview(body()), None):
            with self.assertRaisesRegex(DecodeError, '^body-must-be-bytes$'):
                decode_operation_response(200, data, CONTEXT, OP)
        self.refused(b'', 'body-size')
        doc = document()
        doc['padding'] = ''
        doc['padding'] = 'x' * (MAX_BODY_BYTES - len(body(doc)))
        data = body(doc)
        self.assertEqual(len(data), MAX_BODY_BYTES)
        self.assertEqual(self.decode(data).operation_id, OP)
        self.refused(data + b' ', 'body-size')

    def test_utf8_only_and_json_completeness(self):
        for data in (body() + b'\xff', body().decode().encode('utf-16'), b'\xc0\xaf'):
            self.refused(data, 'invalid-utf8')
        for data in (body()[:-1], body() + b'{}', body() + b' trailing', b'{', b'\xef\xbb\xbf' + body()):
            self.refused(data, 'invalid-json')
        self.assertEqual(self.decode(body() + b' \r\n\t').operation_id, OP)
        for data in (b'null', b'[]', b'true', b'0', b'"value"'):
            self.refused(data, 'invalid-envelope')

    def test_duplicate_keys_at_any_level_including_escapes(self):
        for data in (body()[:-1] + b',"ok":true}',
                     body().replace(b'"id":', b'"id":"discarded","\\u0069d":', 1),
                     body()[:-1] + b',"extra":{"secret":1,"secret":2}}'):
            self.refused(data, 'duplicate-key')

    def test_nonfinite_and_numeric_resource_limits(self):
        for token in (b'NaN', b'Infinity', b'-Infinity', b'1e999'):
            self.refused(body()[:-1] + b',"extra":' + token + b'}', 'nonfinite-number')
        for token in (b'9' * (MAX_NUMBER_CHARS + 1), b'1e' + b'9' * MAX_NUMBER_CHARS):
            self.refused(body()[:-1] + b',"extra":' + token + b'}', 'number-limit')
        self.assertEqual(self.decode(body()[:-1] + b',"extra":1.25}').operation_id, OP)

    def test_depth_and_node_limits_are_string_aware(self):
        doc = document()
        doc['extra'] = '[' * 100 + '\\"' + ']' * 100
        self.assertEqual(self.decode(doc).operation_id, OP)
        leaf = 'value'
        for _ in range(MAX_DEPTH - 1):
            leaf = [leaf]
        doc['extra'] = leaf
        self.assertEqual(self.decode(doc).operation_id, OP)
        doc['extra'] = [leaf]
        self.refused(doc, 'depth-limit')
        doc['extra'] = [None] * MAX_NODES
        self.refused(doc, 'node-limit')

    def test_escaped_surrogates_rejected_but_valid_unicode_allowed(self):
        for value in ('\ud800', '\udfff'):
            doc = document()
            doc['extra'] = value
            self.refused(doc, 'invalid-unicode')
        doc = document()
        doc['extra'] = 'valid snowman \u2603 and \U0001f642'
        self.assertEqual(self.decode(doc).operation_id, OP)

    def test_unknown_fields_ignored_not_echoed_or_trusted(self):
        doc = document('completed')
        doc['secret'] = 'credential-marker'
        doc['account'] = 'untrusted-response-account'
        doc['operation']['private'] = 'credential-marker'
        result = self.decode(doc)
        self.assertNotIn('credential-marker', repr(result))
        self.assertNotIn('untrusted-response-account', repr(result))
        self.assertFalse(hasattr(result, 'account'))
        self.assertFalse(result.authentication_proven)

    def test_all_error_channels_omit_input_and_do_not_chain(self):
        marker = 'credential-marker'
        cases = [body() + marker.encode(), body() + b'\xff' + marker.encode(),
                 body(document(requestedAt=marker)), body(document(id=marker)),
                 body()[:-1] + b',"secret":"' + marker.encode() + b'","ok":true}']
        for data in cases:
            try:
                self.decode(data)
            except DecodeError as error:
                self.assertNotIn(marker, str(error))
                self.assertNotIn(marker, repr(error))
                self.assertNotIn(marker, repr(error.args))
                self.assertNotIn(marker, repr(error.__dict__))
                self.assertIsNone(error.__context__)
                self.assertIsNone(error.__cause__)
            else:
                self.fail('fixture should be refused')

    def test_outer_exception_suppressed_but_context_retained(self):
        marker = 'synthetic-outer-secret-marker'
        cases = ((body() + b' trailing', {}, 'invalid-json'),
                 (body() + b'\xff', {}, 'invalid-utf8'),
                 (body(), {'status': 404}, 'unexpected-http-status'))
        for data, kwargs, code in cases:
            with self.subTest(code=code):
                try:
                    raise RuntimeError(marker)
                except RuntimeError as outer:
                    # Formatting no frame objects keeps this regression free of
                    # source-file reads; the implicit context remains intact.
                    outer.__traceback__ = None
                    try:
                        self.decode(data, **kwargs)
                    except DecodeError as error:
                        self.assertEqual(str(error), code)
                        self.assertEqual(error.args, (code,))
                        self.assertIs(error.__context__, outer)
                        self.assertEqual(str(error.__context__), marker)
                        self.assertTrue(error.__suppress_context__)
                        self.assertIsNone(error.__cause__)
                        formatted = ''.join(traceback.format_exception(type(error), error, None))
                        self.assertIn('DecodeError: ' + code, formatted)
                        self.assertNotIn(marker, formatted)
                        self.assertNotIn(marker, repr(error))
                    else:
                        self.fail('fixture should be refused')

    def test_pure_repeatability_and_immutable_result(self):
        doc = document('completed')
        original = copy.deepcopy(doc)
        first = self.decode(doc)
        self.assertEqual(first, self.decode(doc))
        self.assertEqual(doc, original)
        with self.assertRaises(FrozenInstanceError):
            first.terminal = False
        with self.assertRaises(FrozenInstanceError):
            CONTEXT.response_complete = False


if __name__ == '__main__':
    unittest.main()
