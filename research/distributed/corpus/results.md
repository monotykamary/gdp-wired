3 proven, 7 refuted, 0 unknown, 1 not read or no result

| Service | Language | Patterns | Law | Verdict | Time | Written (comment lines + gdp.toml lines) |
| --- | --- | --- | --- | --- | --- | --- |
| care | Python | lease with expiry | Lock: one holder at a time | broken | 0.3 s | 2 + 5 |
| celery-singleton | Python | lease with expiry, duplicate delivery | RedisBackend: one task at a time | broken | 21.2 s | 2 + 6 |
| huey | Python | lease with expiry | TaskLock: one holder at a time | broken | 0.4 s | 2 + 5 |
| litellm-rc | Python | read-modify-write | _PROXY_MaxIterationsHandler: a call is admitted only while its session is below max_iterations | broken | 0.1 s | 2 + 5 |
| litellm-rc | Python | read-modify-write | _PROXY_MaxIterationsHandler: every call of a limited session counts one, refused or not | broken | 0.1 s | 2 + 5 |
| litellm | Python | read-modify-write | _PROXY_MaxIterationsHandler: a call is admitted only while its session is below max_iterations | proven | 0.6 s | 2 + 5 |
| litellm | Python | read-modify-write | _PROXY_MaxIterationsHandler: every call of a limited session counts one, refused or not | proven | 0.3 s | 2 + 5 |
| membrane | Java | lease with expiry | AcmeMemoryStorageEngine: an expired lease can be taken again | broken | 0.0 s | 2 + 3 |
| membrane | Java | lease with expiry | AcmeMemoryStorageEngine: a lease is prolonged only while it runs | proven | 0.1 s | 2 + 3 |
| opencex | Python | lease with expiry | AutoLock: one holder at a time | broken | 2.4 s | 2 + 8 |
| tork | Go | lock | InMemoryLocker: one holder of a key at a time | not read (the rule was refused) | 0.0 s | 2 + 2 |
