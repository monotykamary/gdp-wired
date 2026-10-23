# The extractor on real code

`gdp-wired/extract` (core/extract.ts) read on code that ships: each source fetched at its pinned commit, extracted, and
checked against itself by running both (core/extract-check.ts); a difference refuses the extraction.

| File | What |
| --- | --- |
| `sources.json` | 22 examples from open-source code (react.dev, redux, statelyai/xstate, rate limiters), each with repo, commit, path and licence |
| `realworld-sources.json` | research/realworld's corpus as of 6c675e4 on research/realworld (its `sources.json`, 41 entries), read as it is |
| `run.ts` | each source extracted (the entry its `export` names, the whole file, its relative imports fetched from the same commit) |
| `verdicts.ts` | each extracted example's laws proven of the extracted rule and of a rule written by hand, the corpus's way |
| `fetch.ts` | the files at their commits, cached in `.cache/` (not committed) |
| `collect.ts` | a batch's logs into `results/` |
| `jobs.json` | the batch: the tests, both lists, the verdicts |
| `results/` | the last batch's (`runs/extract/batch4`, the code of dd80167): `ours.jsonl`, `realworld.jsonl` (one line per source: extracted or refused, where and why, the check's evidence), `verdicts.jsonl`, `rules/` (the rules extracted, as `toSource` prints them) |

```sh
python3 modal/run.py --backend modal --jobs research/extract/jobs.json --out runs/extract/<name> && sh modal/reap.sh
bun research/extract/collect.ts runs/extract/<name>
```

Evidence per extraction (`evidence` in each line): runs from the start and their requests, steps from drawn states,
the prover's witnesses (proveSteps refuting "this condition never holds" for each branch condition over the state and
the request; conditions over a map's cells aren't asked), requests both sides refused, steps past the safe integers
(the code rounds, the rule's runtime refuses), steps where the rule's runtime refuses a sum past 2^53 while the code's
values stay safe (`edge`), the generated JavaScript's agreement with the interpreter, and the branch arms of the code the
step reads that the requests reached. An XState machine is checked by `conforms` (runs from the start, every state and
context compared); its branches are its config's transitions, so the code has none to count.
