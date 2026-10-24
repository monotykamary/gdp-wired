# The interchange format, version 1.0

A rule, its laws and a certificate that they hold, as JSON that any language can read, write and check. gdp-wired
writes it (`toInterchange`, `interchange/format.ts`), reads it back (`fromInterchange`), and checks it with
`gdp-wired-check` (a CLI and a WebAssembly module built from the trusted kernel as it is). The shapes are in
[`interchange/schema.json`](../interchange/schema.json) (JSON Schema 2020-12, every field described); this page says
what a document means and how a checker decides it, closely enough to write a second checker from it.
[`interchange/py/check.py`](../interchange/py/check.py) is one, in Python, written from this page: it checks the trees
of a `goals` document and agrees with the kernel on every goal of the suite.

## A document

```json
{"format": "gdp-wired-interchange", "version": "1.0", "kind": "laws",
 "meta": {"producer": "..."},
 "columns": [{"op": "min", "a": {"op": "var", "name": "used"}, "b": {"op": "var", "name": "cap"}}],
 "machine": {...}, "laws": [...], "proof": {...}}
```

One document is one certificate. `kind` says which fields follow and what they claim. `meta` is the producer's and is
never read by a checker. `columns` is the table of term columns (below). A checker for version 1.m reads every 1.n with
n ≤ m; a minor version only adds optional fields or kinds, a major one changes a meaning. A 1.0 checker refuses any
field it doesn't know.

| kind | fields | claim | decided by (kernel/kernel.ts, kernel/cyclic.ts) | Lean twin |
| --- | --- | --- | --- | --- |
| `goals` | goals: {name, hyps, tree} | each goal's hypotheses never hold together (over the naturals) | `check(goal, tree)` per goal | Kernel.lean `sound` |
| `qgoals` | goals over ℚ | the same over the rationals | `checkQTree` per goal | Rationals.lean `Q.checkGoal` |
| `laws` | machine, laws, proof | every law in every reachable state | `checkLaws` | Kernel.lean `machine_sound`, Sets.lean |
| `stepLaws` | machine, laws, stepLaws, proof | every allowed request (k in a row) does what each step law says | `checkStepLaws` | StepLaw.lean, Steps.lean, Sets.lean |
| `kInduction` | machine, laws, kInduction {law, k}, proof | the law in every reachable state, by k-induction | `checkKInduction` | KInd.lean `kind_sound` |
| `progress` | machine, laws, progress, instances, trees, lawsProof | where `when` holds, the named request is allowed and makes `then` hold | `checkLaws` on lawsProof, then `progressObligations`, a tree each | Progress.lean |
| `liveness` | machine, laws, liveness, proof | `from` leads to `to` under fairness | `livenessParts`, then `checkStepLaws` | Live.lean `leads_sound`, `sleads_sound` |
| `loop` | loop, laws, rank, trees | the loop halts; its invariants hold | `loopObligations`, a tree each | Live.lean `loop_halts_of` |
| `recur` | loop, recur | some run of the loop never ends | `checkRecur` | NonTerm.lean `never_ends_of` |
| `fold` | fold, laws, trees | each law of every tree a fold computes | `foldObligations`, a tree each | Kernel.lean `fold_sound` |
| `cyclic` | cyclic {facts, nodes} | each node's hypotheses imply its conclusion | `refuseCyclic` | Cyclic.lean `cyclic_sound` |
| `qmachine` | machine (over ℚ), laws, trees | every law in every reachable state, the state rationals | `checkQMachine` | Rationals.lean `machine_sound` |
| `termination` | functions, text, measures, obligations | each call of the ring lowers its measure | `refuseCyclic` per obligation | Data.lean (`termination_by`) |

"A tree each" is the kernel's own composition, as `checkLaws` reads trees: the goals the builder makes, each with the
tree the document names for it by the goal's name, every one checked. A set of laws is proven together (each step
assumes them all), so each law of a `laws`, `stepLaws`, `loop` or `fold` document is accepted exactly when the set is.

Two claims rest on a link the format does not carry, and the kernel doesn't check it:
- a `termination` document's obligations are the measures' only given the functions' definitions, which the format
  doesn't hold (core/data.ts's programs): the kernel checks each obligation's cyclic proof, Lean checks the decrease
  under the measures (`termination_by`);
- a `cyclic` document made from a machine (gdp-wired's default certificate) proves its nodes; that the nodes encode the
  machine's laws is Bridge.lean's `cycMOk`, checked in Lean, not by the kernel.

## Values

- **Names**: nonempty strings, not `__proto__`, not a canonical array index (`0`, `7`, `42`: a JavaScript object lists
  such keys before the others, so a record's order would not be its pairs'). A variable read in a linear form has none
  of `* [ ] , :` and is not `1`; the kernel's own names (`x'`, `x~1`, `w@2`, `?f`, `w?f`, `k#`, `r.t`) are variables too.
- **Numbers**: safe integers (|n| ≤ 2^53 − 1), the range the kernel computes exactly in. A term's constant and factor
  are naturals, as Lean's `E` has them. Rationals are `{"num": "-3", "den": "4"}`, decimal strings of any size.
- **Records** are lists of `[name, value]` pairs, in order, each name once, never JSON objects: a machine's state,
  flags and writes, a substitution, a loop's body. The kernel reads several of these in order (a goal's hypotheses are
  built state by state, and a derivation names rows by their place), so the order is part of the value.
- **Terms and conditions** are the kernel's E and C as objects with `op`: `var`, `const`, `add`, `sub` (truncated at
  0), `mul` (by a natural), `prod`, `min`, `max`, `if`, `get` (a map's cell, or a function's value); `<`, `<=`, `=`,
  `and` and `or` of any number of parts, `not`, `flag`, `all`. Over the rationals, `QE` and `QC`: no truncation,
  `mul` by a rational, `and` and `or` binary.

## Linear forms, atoms and columns

A linear form is `[c, [k1, a1], [k2, a2], ...]`: the constant `c` (or `null`: a form with `c = 0` written is another
form, its text differs) and each atom with its coefficient, in the order the kernel built them. An atom is:

| atom | what | the kernel's name for it |
| --- | --- | --- |
| `"x"` | a variable | `x` |
| `{"cell": "M", "key": L}` | map M at the key L (a linear form) | `M[canon(L)]` |
| `{"mono": [a, b, ...]}` | a product of two factors or more, each a variable or a cell | the factors' names sorted, joined by `*` |
| `{"col": i}` | the value of `columns[i]` | `⟦n⟧`, the kernel's number for that term in this process |

`canon(L)` is `name:coef` for each entry, the names sorted by UTF-16 code units, joined by `,` (zero coefficients
kept). A term column stands for the value of a choice (`sub`, `min`, `max`, `if`) that the path where it is read
leaves open; the document names it by its term, since the kernel numbers terms per process. Two equal terms (as JSON
values) are one column.

## Trees and derivations

A tree is `{"split": L, "yes": T, "no": T}` or `{"leaf": [steps], "squares": [L...], "products": [[i, j]...]}`.
`yes` adds the atom `L ≤ 0` to the path, `no` adds `L ≥ 1` (over ℚ, `−L < 0`). A split on an atom the path decides
already, or on a constant, is refused. A step is `["input", i]` (row i of the leaf), `["combine", a, b, ma, mb]` (ma·a +
mb·b, both earlier, ma, mb > 0; strict when either is) or `["cut", of, g]` (an earlier row, g > 0 dividing each of its
variable coefficients: the coefficients divided by g, the constant rounded up; integers only). A leaf is refuted when
its last row has every variable coefficient 0 and a constant > 0, or, strict over ℚ, ≥ 0.

### A leaf's rows, in order

A derivation names rows by their place, so a checker lists a leaf's rows exactly as the kernel does
(kernel.ts's `leafRows`). Lean's twin reads them by value instead (lean-kernel's emitter claims each row a derivation
uses, and Lean finds it among its own), so Lean accepts every tree kernel.ts accepts and may accept one whose rows
moved (a hypothesis changed before them, the rows the derivation reads all still there). A conforming checker follows
kernel.ts: by place. Each row is a linear form read as ≤ 0:

1. the path's atoms, in the order they were decided (`L`, or `1 − L` for a `no`);
2. for each hypothesis in order, its facts under the path (below);
3. for each two cells of one map among the names the rows so far read (in the order first read), whose keys the path
   proves equal (`decide(k1 − k2)` and `decide(k2 − k1)` both true): `c1 − c2` and `c2 − c1`;
4. the term columns those rows read, each once, taken last-in first-out (a list of the columns read, in order; pop
   one, add its rows, push the columns its rows read that aren't done): a `min` column `col − a` and `col − b`; a `max`
   column `a − col` and `b − col`; a `sub` column `(a − b) − col` and `col − a`; an `if` column over two constant
   branches `col − (a + b)`; then, where the path decides the choice, `col − t` and `t − col` for t the branch taken;
5. for every name read so far, in the order first read, `−name` (every value a natural);
6. then the squares (`−t·t`) and the products (`−p·q` for rows p, q, which may be squares or earlier products), in order.

A form's entries are in the order of first appearance as the kernel adds them (`add`, `sub` and `scale` keep the first
operand's order, then the new names, and drop the zeros they make); the constant always comes first. `linear(e)`
under a path: a variable is itself (none of `* [ ] , : ⟦` in its name), a constant `k(c)` (empty when 0), `mul`
scales, `prod` multiplies out (each product of two entries a monomial; no column may appear), `add` adds; `sub`, `min`
and `max` take a branch where the path decides `b − a ≤ 0` (for `sub`, the difference, or `0` when decided false) or
`a − b ≤ 0` (`min` takes `a` when true, `max` `b`), else their column; `if` takes its branch where the condition's
truth is known, else its column; `get` is the cell at `linear(key)`. A form is decided by the path when it is a
constant (`c ≤ 0`), when its canonical text is an atom of the path, or when `1 − L`'s is (the other way).

A condition's truth under the path is Kleene's: a comparison's atoms (`a ≤ b`: `a − b`; `a < b`: `a − b + 1`; `a = b`:
`a − b` and `b − a`) all decided true is true, one decided false is false; `and` and `or` of their parts as usual,
`not` swapped, `all` unknown. A hypothesis's facts: a comparison's atoms when it holds; when it fails, the one way it
can fail that the path hasn't excluded (`b − a + 1` for `≤`, `b − a` for `<`, `a − b + 1` or `b − a + 1` for `=`), or
`1` (refuted) when none is left, none when two are; `and` true gives its parts' facts, `or` true gives the one part the
path hasn't made false (`1` when none, nothing when several), and `not` the other way round; `all` gives none.

Over ℚ (`qgoals`, `qmachine`) the rows are the path's atoms (`L ≤ 0`, or `−L < 0`) and the hypotheses' facts with
their strictness, no naturality rows and no columns: an open choice gives no row. Each form is integers over a
positive denominator, computed exactly; a row past 2^53 is left out.

## What a kind's goals are

The goals of the machine kinds are built from the machine by the kernel's functions (named in the table), and their
names are the kernel's: `<law> @start` and `<law> @step` for a law; `<step law> @step law` or `@<k> steps`; a k-induction's
`<law> @start`, `<law> @base <j>` and `<law> @k-step`; a history's `relation <i> @record` and `prune @query <q>`; a
cyclic node's own, `use <j>, its hypothesis <i>` and `its rank below`. A checker in another language can either build
the goals (kernel.ts says how, each step in prose, and the Lean twin builds the same ones) or take them from
`gdp-wired-check --goals out.json doc.json`, which writes a certificate's goals with their trees as a `goals` document:
the tree part of every check, the part a second checker can take alone.

## Reading faithfully

`gdp-wired-check` reads a document into the kernel's objects, writes them back, and refuses the document unless the
two agree (as JSON values, each column reference replaced by its term). So what the kernel checks is what the document
says: a field the reader dropped or a value it changed would show as a difference. A round trip from the kernel's
objects is the identity on everything the kernel reads; JSON has no `-0` (read as 0, as the kernel reads it) and no
`undefined` (a field holding it is no field).

## Checking it

```sh
bun interchange/build.ts --wasm                      # dist/gdp-wired-check.js and .wasm (JAVY=<javy 9.1.0>)
node interchange/dist/gdp-wired-check.js doc.json    # accepted or refused, per claim; --json; exit 0 when all accepted
wasmtime run interchange/dist/gdp-wired-check.wasm < doc.json
python3 interchange/py/check.py goals.json           # the second checker, on a goals document
```

The conformance runs are in `interchange/` (capture.ts takes every certificate a suite run hands the kernel, verify.ts
checks each again with the bundle, the module and the second checker, tampered three ways; lean.ts sends the
conformance cases to Lean through the same documents), and their numbers in the CHANGELOG.
