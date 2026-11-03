# Runtime-only corroboration of the published OAuthlib client-identity issue.
# This is not a prover result and never changes scoreRecall's admission rules.
import json
import sys
from types import SimpleNamespace
sys.path.insert(0, sys.argv[1])
from oauthlib.common import Request
from oauthlib.oauth2 import ClientCredentialsGrant, RequestValidator
from oauthlib.oauth2.rfc6749.errors import OAuth2Error

class Validator(RequestValidator):
    def __init__(self):
        self.authorized_ids = []
    def authenticate_client(self, request, *args, **kwargs):
        request.client = SimpleNamespace(client_id='low')
        return True
    def validate_grant_type(self, client_id, grant_type, client, request, *args, **kwargs):
        self.authorized_ids.append(client_id)
        return grant_type == 'client_credentials'
    def validate_scopes(self, client_id, scopes, client, request, *args, **kwargs):
        self.authorized_ids.append(client_id)
        permitted = {'read', 'admin'} if client_id == 'high' else {'read'}
        return set(scopes or []) <= permitted
    def get_default_scopes(self, client_id, request, *args, **kwargs):
        return ['read']

def attempt(requested_id, scope):
    validator = Validator()
    request = Request('https://example.invalid/token', http_method='POST',
                      body='grant_type=client_credentials&client_id=' + requested_id + '&scope=' + scope)
    try:
        ClientCredentialsGrant(validator).validate_token_request(request)
        accepted, error = True, None
    except OAuth2Error as exc:
        accepted, error = False, type(exc).__name__
    return {'accepted': accepted, 'authenticated_id': getattr(request.client, 'client_id', None),
            'requested_id': requested_id, 'authorized_ids': validator.authorized_ids, 'error': error}

version = sys.argv[2]
control = attempt('low', 'read')
attack = attempt('high', 'admin')
assert control['accepted'], control
assert attack['accepted'] == (version == 'vulnerable'), attack
assert attack['authenticated_id'] == 'low', attack
if attack['accepted']:
    assert attack['authorized_ids'] and set(attack['authorized_ids']) == {'high'}, attack
print(json.dumps({'kind': 'runtime-only-not-CLI-recall', 'version': version, 'control': control, 'attack': attack}))
