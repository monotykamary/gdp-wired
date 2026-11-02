# The regulated corpus: privacy and deadline laws on real code

ROADMAP.md §6.3's measure is "one open-source workflow's privacy and deadline laws decided". This corpus takes real
healthcare and privacy code with permissive licences through the path a user takes:
- the files at a pinned commit;
- the laws as `gdp: law` comments, each with a `gdp: cite` to the public clause it answers;
- gdp.toml only where needed;
- `gdp-wired check` on the target.

The cited clauses are HIPAA's 45 CFR, GDPR, the CCPA regulations and RFC 6749. A citation names the clause a law
answers; it never claims the law, or the code, is faithful to it.

**Where it stands: the measure is not met on code as it ships.** The readers refuse every one of the eight targets
below, so none of the 11 laws stated is decided. A scan of 40 healthcare and privacy repositories, run the same way,
shows why: almost none of this code is in the readers' subset. The pieces the measure needs around the code are built
and checked:
- laws about two runs;
- deadlines in calendar days and business days (core/calendar.ts);
- citations, drafting and sign-off (../DRAFTING.md);
- certificates checked in Lean.

What is missing is the readers' reach, ranked below by how much code each gap blocks.

    bun research/regulated/corpus/fetch.ts                         # each item's files at its commit, into .cache/ (not committed)
    bun research/regulated/corpus/run.ts <item> --out <dir>        # one item, as a user runs it
    bun research/regulated/corpus/jobs.ts > jobs.json              # the suite, one job per item
    supercomputer run --jobs jobs.json --out runs/regulated/<name> --class gate --data research/regulated/corpus/.cache:research/regulated/corpus/.cache
    bun research/regulated/corpus/collect.ts runs/regulated/<name> --write     # results.md, results.json

## The items

Each item is three files under `items/<name>/`:
- `item.json`: the repository, commit, licence, files and target;
- `laws.patch`: what the user writes, comments only (run.ts refuses a patch that adds anything else);
- optionally `gdp.toml`.

The code itself isn't vendored. Each patch quotes three lines of context around each comment.

| Item | Code | Laws (privacy; deadline) | Clauses | Refused at |
| --- | --- | --- | --- | --- |
| smart-client-py | smart-on-fhir/client-py `FHIROAuth2Auth` (Python) | a reset token is gone; an expired token never signs | 45 CFR 164.312(a)(1); RFC 6749 §5.1 | `expires_at = "datetime \| None"` in gdp.toml: a datetime is no stated type (the field is set to None in `__init__`) |
| bluebutton-grants | CMSgov/bluebutton-web-server `DataAccessGrant` (Python) | a grant past its expiration date has expired; the rolling window ends 90 days on | 45 CFR 164.508(c)(1)(v) | `self.application`: a Django model's fields are class attributes, not set by a constructor |
| bluebutton-patient | CMSgov/bluebutton-web-server `is_resource_for_patient` (Python) | another patient's record is never released | 45 CFR 164.502(a) | `obj['resourceType']`: a FHIR resource is an untyped dict |
| django-session-timeout | labd/django-session-timeout `SessionTimeoutMiddleware` (Python) | a session past its time is ended | 45 CFR 164.312(a)(2)(iii) | `hasattr(request, 'session')`; the state is the request's session, not the object's |
| hapi-consent | hapifhir/hapi-fhir `IConsentVote.parallelReduce` (Java) | a rejection always wins | 45 CFR 164.508(b)(5) | a static generic method of an interface |
| fhir-gateway-scopes | google/fhir-gateway `SmartScopeChecker` (Java) | no scope, no access | 45 CFR 164.502(b)(1) | a map of sets built by streams in the constructor |
| fides-gpc | ethyca/fides `calculateAutomatedConsent` (TypeScript) | GPC is honoured where nothing was saved | Cal. Code Regs. tit. 11 §7025(b) | a function of its arguments (a decision): the TypeScript reader reads steps over a state only |
| orejime-consent | empreinte-digitale/orejime `Manager` (TypeScript) | declining withdraws every optional consent; a withdrawal takes effect | GDPR Art. 7(3) | `#listeners`: an ES private field in its base class (read beside it since this lane) |

**What the user writes.** It is 2 to 4 comment lines per item: each law and its citation. Only smart-client-py adds
gdp.toml, 3 lines: its methods, and the types of the fields its constructor sets to None. Every item is refused in 0.3
to 5.3 s. The verdicts and times are in `results.md` (`runs/regulated/corpus3`).

**What was flagged.** Reading these files turned up several places where the code may not meet the clause cited. None
is a refuted law, since nothing was read, and none is reported here. Each is noted privately for a check by hand.

## The scan: how much of this code the readers take

`scan.sh` and `scan-functions.sh` run the CLI as a user would, on boat, one job per repository (`runs/regulated/scan1`,
`scan2`):
- `scan.sh`: every file under 700 lines whose path names consent, access, permission, expiry, retention, audit,
  policy, scope, session, token, lock, grant, revocation, claim, auth, limit or eligibility (tests, mocks and
  migrations excluded), with no entry named.
- `scan-functions.sh`: every top-level function of such Python files, read as a decision (`--entry <function>`), after
  installing the repository's requirements.txt where it has one.

**Files** (40 repositories at their default branch's head, 3,788 files): 3 read, all of them trivial (Ory's
configx `ImmutableError`). Of the rest:

| Why | Files |
| --- | --- |
| no class or struct writes its state: stateless functions, handlers, services over a database | 1,531 |
| another construct outside the subset (loops, untyped dicts and lists, strings beyond set and compared, `hasattr`, comprehensions, closures, ...) | 1,158 |
| another module's code, or a dependency the check can't load | 441 |
| a function of its arguments (a decision), in TypeScript, JavaScript or Go, which read steps only | 275 |
| an interface, or another module's type (Go especially) | 244 |
| no answer within 90 s | 48 |

The repositories: the CMS's Blue Button, BCDA, AB2D, DPC, BFD, EASi and MINT; HL7 Da Vinci's CRD and prior-auth reference implementations;
Synthea; Google's fhir-gateway and android-fhir; Medplum; the SMART client-js and client-py; Cumulus; Tidepool's
platform, shoreline and hydrophone; fhir-works-on-aws authz-smart; node-fhir-server-core; OpenSRP fhircore; Fides
and fideslang; Orejime, Klaro and cookieconsent; DefectDojo; django-otp, django-axes, django-prbac and
django-session-timeout; Ory Hydra and Kratos; node-oidc-provider; Ballerine; Tazama; moov's watchman. All are MIT,
Apache-2.0, BSD or CC0. The commits are in the scan's logs.

**Python functions as decisions** (14 repositories, 1,108 functions): 1 read (Blue Button's `list_to_text`). The rest
read untyped dicts and lists, call `hasattr` and `getattr`, use comprehensions, or import what the check can't load.

## What the measure needs next

Ranked by what the scan says it unblocks. Each is a reader's reach, not the prover's.
1. **Decisions in TypeScript, JavaScript, Java and Go**, as Python has them: one call a request, its result kept.
   Most privacy rules are permit-or-deny functions (fides-gpc, Medplum's access policy, HAPI's votes). 275 files are
   refused for exactly this, and many of the 1,531 have nothing else.
2. **State held outside the object.** This covers a model's row (Django or SQLAlchemy class attributes, `self.save()`)
   and the request's session. Blue Button's grants, DefectDojo's SLAs, Fides's privacy requests and the session
   timeout all keep their deadlines there.
3. **Untyped records.** A FHIR resource or a token response is a dict with string keys, read by key. Typing one by
   `gdp.toml` (`types` for a dict's keys) would take Blue Button's patient check and the SMART client's token
   response.
4. **A datetime field.** A datetime is read today as a value in a step (`datetime.now()`, `timedelta`), but not as a
   field's type. The SMART client's `expires_at` needs that.
5. **Lists of records and loops over them** (consents per purpose, notices, scopes), and ES private fields.

Each item above names its first refusal only, and a reader that gets past it may stop at the next. For example,
fides-gpc loops over the notices after its decision is read. The corpus is the test of each step: an item's laws are
decided when its reader takes it, with nothing written but the comments and gdp.toml.
