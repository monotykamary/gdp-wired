# The regulated corpus: verdicts (corpus3)

8 codebases, 11 laws: 0 proven, 0 broken, 0 unknown, 11 not read.

| Item | Language | Rule | Law | Verdict | Time | Cites |
| --- | --- | --- | --- | --- | --- | --- |
| bluebutton-grants | Python | DataAccessGrant (refused) | the rolling window ends 90 days on | not read | 0.0 s | 45 CFR 164.508(c)(1)(v): "…" |
| bluebutton-grants | Python | DataAccessGrant (refused) | a grant past its expiration date has expired | not read | 0.0 s | 45 CFR 164.508(c)(1)(v): "…" |
| bluebutton-patient | Python | is_resource_for_patient (refused) | another patient's record is never released | not read | 0.0 s | 45 CFR 164.502(a): "…" |
| django-session-timeout | Python | SessionTimeoutMiddleware (refused) | a session past its time is ended | not read | 0.0 s | 45 CFR 164.312(a)(2)(iii): "…" |
| fhir-gateway-scopes | Java | SmartScopeChecker (refused) | no scope, no access | not read | 0.0 s | 45 CFR 164.502(b)(1): "…" |
| fides-gpc | TypeScript | calculateAutomatedConsent (refused) | GPC is honoured where nothing was saved | not read | 0.0 s | Cal. Code Regs. tit. 11, § 7025(b): "…" |
| hapi-consent | Java | IConsentVote (refused) | a rejection always wins | not read | 0.0 s | 45 CFR 164.508(b)(5): "…" |
| orejime-consent | TypeScript | Manager (refused) | declining withdraws every optional consent | not read | 0.0 s | GDPR Art. 7(3): "…" |
| orejime-consent | TypeScript | Manager (refused) | a withdrawal takes effect | not read | 0.0 s | GDPR Art. 7(3): "…" |
| smart-client-py | Python | FHIROAuth2Auth (refused) | a reset token is gone | not read | 0.0 s | 45 CFR 164.312(a)(1): "…" |
| smart-client-py | Python | FHIROAuth2Auth (refused) | an expired token never signs | not read | 0.0 s | RFC 6749 section 5.1, expires_in: "…" |

| Item | Rule | Refused where | Why |
| --- | --- | --- | --- |
| bluebutton-grants | DataAccessGrant | models.py:53:12 | self.application: no field application (the object's fields are those its constructor sets) |
| bluebutton-patient | is_resource_for_patient | permissions.py:47:12 | obj['resourceType']: an item of obj: a value of no type the code states (whether it holds one is that value's) |
| django-session-timeout | SessionTimeoutMiddleware | middleware.py:15:16 | hasattr(request, 'session'): hasattr() (a builtin outside the subset) |
| fhir-gateway-scopes | SmartScopeChecker | SmartScopeChecker.java:44:3 | hasPermission returns this.permissionsByResourceType .getOrDefault(resourceType...: the value of permissionsByResourceType.getOrDefault(resourceType, Collection |
| fides-gpc | calculateAutomatedConsent | automated-consent.ts:34:42 | calculateAutomatedConsent is not a step over a state (a step takes the state first and returns the next): it takes PrivacyExperience and returns { noticeConsent |
| hapi-consent | IConsentVote | IConsentVote.java | no class or function IConsentVote in IConsentVote.java |
| orejime-consent | Manager | EventEmitter.ts:6:2 | #listeners: a #private field (the check reads the object's fields; `private` is in the subset) |
| smart-client-py | FHIROAuth2Auth | auth.py:145:1 | the answer type "datetime / None" (int, float, bool, str or quoted strings, each with / None) |

| Item | Repository | Commit | Licence | Written (comments, laws, cites, gdp.toml lines) | Wall |
| --- | --- | --- | --- | --- | --- |
| bluebutton-grants | https://github.com/CMSgov/bluebutton-web-server | 7dd4642eb9 | Apache-2.0 | 4, 2, 2, 2 | 0.8 s |
| bluebutton-patient | https://github.com/CMSgov/bluebutton-web-server | 7dd4642eb9 | Apache-2.0 | 2, 1, 1, 0 | 0.3 s |
| django-session-timeout | https://github.com/labd/django-session-timeout | 0fb35d012b | MIT | 2, 1, 1, 0 | 0.4 s |
| fhir-gateway-scopes | https://github.com/google/fhir-gateway | cac059dbec | Apache-2.0 | 2, 1, 1, 0 | 2.6 s |
| fides-gpc | https://github.com/ethyca/fides | e87f3ff835 | Apache-2.0 | 2, 1, 1, 0 | 0.5 s |
| hapi-consent | https://github.com/hapifhir/hapi-fhir | 2478334211 | Apache-2.0 | 2, 1, 1, 0 | 4.9 s |
| orejime-consent | https://github.com/empreinte-digitale/orejime | 70a42c4b4b | BSD-3-Clause | 4, 2, 2, 0 | 1.0 s |
| smart-client-py | https://github.com/smart-on-fhir/client-py | ee5ea26774 | Apache-2.0 | 4, 2, 2, 3 | 0.2 s |
