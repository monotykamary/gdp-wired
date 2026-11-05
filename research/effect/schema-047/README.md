# Schema 0.47 development evidence

Worktree: `gdp-wired-effect-schema-047`, branch `feat/effect-schema-047`, based on
`156cd29994815ba3370ba97909c8e4192ca0d2bc`. This is a frontend candidate, not a release.
No kernel/DSL changes, protocol runs, publishing, pushes or other worktree edits.

All runtime inspection, tests, lint, builds and package consumers ran on Boat with `--backend boat`.
Local work was git, file edits/copies and bounded inspection only. No external cloud fallback.

## Initial probes (do not count the failures as tests)

- `20261105-211458-as2gqh`, tree `47fe2a312b7f`, job `schema047-ast-baseline`: exit 1,
  inline shell quoting error. **NOT_RUN** as tests. Original receipt/output: `probe-v1.log`.
- `20261105-211618-onuqru`, same tree, job `schema047-ast-v2`: exit 1, invalid dynamic
  Effect 3 Class invocation after partial Effect 4 AST output. Not a passing probe/test: `probe-v2.log`.
- `20261105-211720-jtx546`, tree `03528285aef1`, job `schema047-probe-v3`: exit 0.
  The saved `../schema-probe.ts` inspects both versions and reads their Int implementation;
  `probe-v3.log` confirms `Number.isSafeInteger`, rejecting fractions, NaN, infinities and ±2^53.
  Permanent boundary regressions are in `core/effect-schema.test.ts`.

The probes requested 1 CPU and **3 MB**, and early checks 2 CPUs/**6 MB** (not GiB). This resource-unit mistake
was identified by Main and not hidden or used for a timing claim. Later runs use MB explicitly.

## Intermediate checks

- `20261105-212239-t5xqsr`, tree `96ace091a24c`: schema tests passed (10 / 2052 assertions),
  but TypeScript failed on new errors and missing vendor imports. This was **not a green candidate**.
- `20261105-212804-fmk762`, tree `55ce9f614722`: scoped TypeScript (including negative `.types.ts`),
  scoped type-aware lint, schema tests (12 / 2106 assertions) and CI unit registration passed.

## Frozen v3 complete requested groups

Batch `20261105-213000-223p29`, tree `1d4bab97d0f0`; commands/resources in `jobs-v3.json`,
placement in `placement-v3.json`, terminal summary in `summary-v3.tsv`. Both jobs requested
2 CPUs and **6 MB**, shared the same non-exclusive `large` VM `bx_85wyqdj5`. No performance or isolation claim.
Source remained frozen until both jobs were terminal.

- `schema047-suites-v3`: exit 0. Schema group exit 0; full four existing Effect test files 35 pass/0 fail;
  eight relevant DSL/kind/runtime files 58 pass/0 fail; existing Effect example pass; exports 22 pass/0 fail.
  `suites-v3.log` is the retained receipt/log; its stderr begins mid-line because the runner bounded its tail,
  so do not infer an exact assertion count for the earlier schema group from this log.
- `schema047-quality-v3`: exit 1, **not a whole-repository green**. Scoped TS/lint, declaration build,
  original Effect-absent tarball smoke, separate Effect 3.22.4 and 4.0.7 tarball runtime/type consumers,
  and CI registration each exited 0. Full repo TS failed on missing vendor modules and consequent implicit-any
  errors; repo lint failed at existing `research/hw/run-more.ts:78` (`no-redundant-type-constituents`).
  Commitlint invocation failed because `--edit` tried to locate a git root in the Boat snapshot; the message
  was not linted. Full details in `quality-v3.log`; the invocation is corrected to file-fed stdin next.

After v3, review identified a generic typing gap for branded strings and narrowed predicates. V3 is **not**
the final typed API: the follow-up keeps exact representation selection on structural `Encoded`, and makes
all explicit/possible approximations `SchemaKind<unknown>`. No assertion-cast convenience API is provided.

## Final conservative type boundary and package validation

- `20261105-214231-byl7jh`, source tree `abce0e91db1e`, job `schema047-types-v4`: exit 0.
  Scoped TypeScript includes `core/effect-schema.types.ts`; lint passes; 14 schema tests / 3342 assertions pass.
  This covers both-version exact branded String/literal/nested/tagged inference and runtime behavior, and
  negative type checks that explicit/possible approximation yields unknown. Saved in `types-v4.log`.
- `20261105-214422-dyaruv`, **same source tree** `abce0e91db1e`: both final jobs exit 0.
  `schema047-final-core-v4`: 40 tests / 3575 assertions across schema, existing Effect service integration,
  datatypes, values and builders. `schema047-final-package-v4`: scoped TypeScript, scoped lint, declaration build,
  original Effect-absent smoke, isolated Effect 3.22.4 and 4.0.7 packed runtime/TS consumers (including branded
  strings/literals and unknown approximation), export/package tests and corrected file-fed commitlint all exit 0.
  See `jobs-v4.json`, `summary-v4.tsv`, `placement-v4.json`, `core-v4.log`, `package-v4.log`.
  Both requested 2 CPUs/**6144 MB**; placement allocated 4 vCPUs per job on one shared `large` VM (not exclusive).
- The full existing Effect schedule/STM/queue groups and eight-file DSL set are the completed **v3** runs above;
  after v3 the implementation changes were type aliases/overloads only, with additional tests/docs. They were
  not relabeled as full v4 executions. Main owns any further full release run.
- Whole-repo TS/lint failures above remain visible and unresolved; the final job is not a claim that the entire
  repository is green. Package/library versions remain 0.46.0; 0.47 is only the changelog draft.

After the final frozen run, only these evidence copies and this outcome note were added. No tested implementation,
example, type test, runtime test, build/export setting or package script was changed.
