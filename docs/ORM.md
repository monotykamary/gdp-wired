# ORM-backed handlers

The Python and TypeScript readers can read a deliberately bounded subset of handlers over a database. A model
is a keyed table, and a handler is a step over shared map state. A query does not invent an independent input:
it reads the table. A fetched row is detached; mutating it does not persist it until a supported save/commit.

This is a **persistence boundary**, not verification of an ORM or database implementation. The differential check
runs the original module's handlers and model methods, replacing persistence with dictionary-backed substitutes.
It creates no database tables. Importing the original module can execute its initialization and imports; the
checker is not a sandbox. Database constraints beyond primary-key existence/uniqueness, triggers, signals, default
factories, database-specific coercions and effects outside this boundary are not established by a proof.

## Python

Use `extractPython(path, {entry: ['create', 'credit']})`, or `gdp-wired check` with entries in `gdp.toml`.
The reader resolves imported model/column names without executing them. The check needs the project's Python
dependencies installed. `python` selects an interpreter; `djangoSettings` (or the environment's
`DJANGO_SETTINGS_MODULE`) selects settings, followed by `django.setup()` before importing the module.

- Django `models.Model`: integer, boolean, character/text and datetime columns; `null=True` is optional.
- SQLAlchemy `declarative_base()` and `DeclarativeBase`: `Column` and typed `Mapped[T] = mapped_column(...)`.
  Integer, boolean, string/text and datetime columns are supported. Nullability is retained.
- Model methods can read/write explicitly supplied columns. All constructor columns are parameters, not assumed
  defaults. No arbitrary row is claimed to have been loaded from a real database.
- Django `Model.objects.get(pk=k)` (or the declared primary-key name), keyed `filter(...).first()` and `.exists()`,
  `create`, `row.save()`, `row.delete()` and keyed queryset deletion use table state. Creation requires every column,
  including an explicit primary key. Saves preserve detached-copy behavior; deleting a Django row clears its key.
- Typed SQLAlchemy `Session` arguments support a bounded `get`, `add`, `delete`, `commit` flow. Writes persist at
  commit. Multiple reads of one table (identity-map semantics), calls after commit and database exception handlers
  are refused rather than approximated.
- Datetime columns are milliseconds. Django datetime parameters/rows in this subset are UTC-aware; SQLAlchemy's
  `DateTime(timezone=True)` is UTC-aware and plain `DateTime` is naive. `datetime.now(timezone.utc)` is supported.
  `relativedelta` supports named fixed durations (days, weeks, hours, minutes, seconds, milliseconds), not calendar
  months/years or absolute replacements. Mixing naive and aware datetime ordering is refused.

Non-primary-key scans, composite keys, foreign-key traversal, inherited table schemas, custom managers and custom
persistence overrides are refused. Decorated model classes/methods, custom magic methods and cross-session row
transfers also refuse. Before replacing persistence, the harness validates the original framework methods and
constructors; a custom hook such as Django `save_base` must not be hidden by the replacement. Numeric map keys
must be nonnegative in the source's behavior; an unchecked
`domains` narrowing is not a substitute for that behavior. String keys do not need this restriction.

## Explicit Python datetime boundaries

The general Python reader also accepts `types` and `answers` entries such as `"datetime | None"`,
`"datetime-naive | None"` and `"datetime-utc | None"`. These are explicit boundary declarations, not a guess from
Python's broad `datetime` annotation: `datetime` aliases naive datetime here; `datetime-utc` selects UTC-aware
values. The admitted values are millisecond-aligned and within Python's datetime range. The extraction notes
record this scope. Naive datetime boundaries and naive `datetime.now()` clocks also require a UTC process timezone;
a non-UTC process is refused rather than silently reinterpreting local time. Arbitrary timezone rules and
sub-millisecond values are not silently rounded into this model.

Optional state, constructor/method arguments and answered calls retain `None` separately from the timestamp.
The harness constructs actual Python datetime values, including UTC awareness where stated; mixed naive/aware
ordering refuses. Native datetime annotations alone do not establish timezone or precision and remain outside
this extension. A law proved for this stated boundary must not be presented as covering every Python datetime.

## TypeScript: Prisma and TypeORM

```ts
import {extract} from 'gdp-wired/extract'
const result = extract('handlers.ts', {
  entry: ['create', 'read'],
  orm: {schema: 'schema.prisma', model: 'Account'},
})
```

The `orm` option is also accepted through `gdp.toml`:

```toml
entry = ["create", "read"]
env = "read committed"
[orm]
schema = "schema.prisma"
model = "Account"
kind = "prisma"
```

The schema path is relative to the handler module. `kind = "typeorm"` selects a TypeScript entity file with
import-resolved `@Entity()`, `@PrimaryColumn()` and `@Column()` declarations. Schemas require one explicit primary
key and scalar columns; defaults, relations, composite keys and unsupported decorators/types refuse.

Exported functions, or `Service.method` on a supported exported class with no custom constructor, take the injected
client/repository as their first argument. Other arguments have scalar TypeScript annotations. The subset supports
awaited Prisma `findUnique`, `update`, `create`, and TypeORM `findOneBy`, `save`. Nullable reads currently must be
immediately dereferenced in the final return; other null-handling control flow refuses. Writes specify explicit
columns; unsupported calls/expressions refuse. A Bun subprocess imports and asynchronously calls the original
module; it does not compare two translations of the handler.

## Environment and evidence

Table map families are exposed in `Extraction.names` as stores. `gdp: env` / `env` in configuration lifts them into
`core/system.ts`'s atomic, read-committed or snapshot model. This is an explicit environmental assumption, not inferred
from an ORM's default transaction settings. The differential check covers the sequential handler; the system model
supplies the stated interleavings. Expiry, retries and other supported environment words retain their existing meaning.

`core/extract-py-orm.test.ts` and `core/extract-orm.test.ts` cover original-code differential execution, safe refusals,
nullable columns, persistence, service methods and map invariants. Wider application code may still be refused.
A successful synthetic fixture does not establish a law about a third-party application: each law needs its own
extraction and proof, or a counterexample reproduced on that application's real code.
