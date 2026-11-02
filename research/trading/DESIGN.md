# Trading: ordered collections and fixed-point rounding (gen/laneO)

Step 5 of research/ROADMAP.md: "price-time priority" as a law (every fill matches the best price, the earliest at that
price) over a structure laws can talk about, and rounding to a tick, soundly. The measure: an open-source matching
engine's priority law decided with nothing written but the laws, the rule checked against the code by running both,
every refuted law replayed in the real code.

## The structure: a keyed map and its least key

An ordered collection (a sorted map's first entry, a heap's top, a priority queue, a list's first item) is a keyed map
plus one term: **the least key** where a condition holds, by a lexicographic order of terms of the cell
(`core/dsl.ts`'s `Rule.least`, `desc`):

    .least({best: ({Asks}) => ({where: k => Asks.at(k).has, by: k => [Asks.at(k).price, Asks.at(k).seq]})})

`best` is a `Maybe` (none where no key meets `where`). Nothing new reaches the kernel: to it `best` and `best$some` are
two inputs, and what makes `best` the least is the rule's assumption, conditions about every key the kernel already
decides (EPR with order):

    some ⇒ where(best)        ¬some ⇒ ∀k ¬where(k)        some ⇒ ∀k where(k) ⇒ by(best) ≤lex by(k)

The runtimes find it (`core/machine.ts`'s `Machine.leasts`, `leastsIn`, and the same scan in `compileJs`): the keys the
maps read hold cells at, the smaller key where all tie; a condition that holds past every cell has no least, and the
request is refused. The runtimes check the assumption before a step as for any request (`allowed`, and the generated
code's guard), so a wrong scan could only refuse, never run a step no proof covers. A part may be an `Int` (two
naturals, `e − neg`) and may be compared the other way (`desc`).

Considered and not taken: a kernel kind for ordered maps. The least key needs none, and the assumption is the whole
meaning of "least", so the trusted code is unchanged (kernel/, core/check.ts, lean-kernel/: no diff).

**examples/orderbook.ts** (written in the DSL): a continuous double auction, each resting order a cell keyed by its id,
the best bid and ask least keys. Proven: "an ask fills the best bid: none higher, none at its price earlier", the same
for bids, and "the book never crosses" (every bid below every ask, a law over every two keys, inductive through the
assumption alone). Refuted: bids ranked by the lowest price (both laws), arrival ignored at a price (priority).
core/orderbook.test.ts: the proofs (about 8 s), and the runtimes against a scan of the book on 2,400 steps (interpreted
= compiled, every request with a fresh id allowed).

## Reading it from code: a list of the state

Python's list of records (or numbers) the constructor makes empty (`self.bids: list[Order] = []`) is read as a map keyed
by each item's **place**, a natural that only grows as items are added (core/extract-step.ts, `MapDecl.ordered`):
removing an item leaves the others' keys, so the order of the keys is the list's order, and a law can name an item
across a step. What the subset reads, each on the least keys:

| Code | Read as |
| --- | --- |
| `xs.append(x)` | a write at one place past the greatest key (0 when empty) |
| `xs.remove(x)` | the first item equal to x (a dataclass's fields; another `__eq__` refused): the least key where every field equals; none, a ValueError |
| `xs.pop()`, `xs.pop(0)`, `xs[-1]`, `xs[0]` | the greatest or least place; an empty list, an IndexError |
| `min(xs, key=lambda o: (...))`, `max(...)`, `default=` | the least key by the key's parts (a tuple's, lexicographic; `-x` the other way), then by place: Python's first of those that tie |
| `if xs`, `not xs` (and a dict's) | whether any key is held |
| `min(d)`, `max(d)` of a dict keyed by numbers | its least or greatest key |

A least key is read in the state before the step (one read after the step wrote its list is refused), each once
however often the code reads it, and two orders over the same keys share whether there is one, so a path that took one
knows the other is there (what makes `self.asks.remove(ba)` after `ba = min(self.asks, ...)` never fail). An item taken
out keeps its fields (a value the code read from it is still the object it holds). Refused, each where it is: a list
read at another place, a list literal with items, a lambda anywhere but min's or max's key, `len`, `insert`, `sort`,
a comprehension.

Two smaller pieces the engine needed, general to the reader: a **string field the module only sets to literals** (every
construction of the record gives one) is a choice of them, said in the notes; and a **true division** (`a / b`) is a
float kept opaque, refused only where the rule reads it (its divisor 0 a ZeroDivisionError), as other values outside the
subset are. Before, both refused the whole class.

The check (core/extract-check.ts, core/py/harness.py) compares a list by its items in order: the rule's held keys
sorted, the code's list as it is; a state given to both is the list in key order.

**Laws over items** (core/laws.ts): `forall o in old(self.asks): forall j in old(self.asks): ...` at every two (or
three) at once; `o.price` an item's field; `o in self.asks` whether that item is still in the list (the same item, not
an equal one); `o <= j` the list's order (o was put in no later than j).

## Fixed-point rounding

Integer division by a constant was already exact (`//`, `%`, `math.floor(a / k)`, `int(a / k)`; the IR's `divk`/`modk`,
a variable with k·q ≤ a < k·q + k). Added: Python's **`round(a / k)`**, to the nearest, a half to the even one, exact
for |a| below 2^53 (the float a / k is within half its last place of a / k, which is less than 1/(2k), so it lands on a
half only where a / k is one); `round(x)` of a whole number is itself. core/rounding.test.ts: a quoter putting prices
on a tick of 10 by a floor and by round, its laws proven (on a tick; at most the price; within a tick; within half a
tick), and "a half never rounds down" broken at p = 25 (round(2.5) is 2), the run replayed in Python.

The kernel reads a division only in a law about every state, not in a law of one step (its step-law scope reads maps,
not functions: kernel/kernel.ts:1316), so "on a tick" is stated as an invariant there. Exact rationals (core/rationals.ts)
cover decimal prices; a floor of a rational is mixed-integer arithmetic, not taken.

## Measured: Mesa's continuous double auction

The engine: mesa/mesa-examples `examples/zi_double_auction/model/order_book.py` at 5ab1c41 (Apache-2.0, sha256
54d2f782…), the order book of Mesa's zero-intelligence continuous double auction: two lists of `Order` dataclasses, the
best bid `max(bids, key=lambda o: (o.price, -o.timestamp))`, the best ask `min(asks, key=...)`, `try_match` removing
both where they cross. Read as it ships (research/trading/mesa.ts: the pinned file with the comment laws above
`try_match`, nothing else), the rule checked against the code by running both, on Modal (2 vCPU, 30 s a law):

| Law (on try_match) | Verdict | The run, replayed in the real code |
| --- | --- | --- |
| the best bid fills: no bid higher, none at its price with an earlier timestamp | proven, also from every state with no invariant | |
| the best ask fills | proven, also from every state | |
| a fill crosses: the ask's price at most the bid's | proven, also from every state | |
| the earliest to arrive at the best price fills | broken | two asks at price 1, the later one stamped time −6: the engine's time priority is the caller's timestamp, not arrival; broken in the code too |
| no agent trades with itself | broken | an agent's bid and ask that cross are matched with each other; broken in the code too |

The read took 82 s (the check's runs and the laws together); each law 9 to 23 s. Notes the reading printed: `Order.side`
a choice of "ask" and "bid"; the lists read in order; `try_match`'s `time` read by no term.

**The boundary.**
- **Methods.** `--methods submit_bid,submit_ask,best_bid,best_ask,spread,try_match` is stated: `clear_all_crosses` is a
  loop over `try_match` (a loop over the state; Lane L's folds read a loop over a list the request carries, not this)
  and `cancel_agent_order` rebuilds a list chosen by a condition from a comprehension (an alias of two lists by a
  condition, and a write at every place). The three proven laws hold from every state of the lists with no invariant
  beside them, so they hold in runs that call those two as well: `clear_all_crosses`'s steps are `try_match`'s, and
  `cancel_agent_order` only removes items. That argument is ours, not checked by the tool.
- **Floats.** Prices and timestamps are floats; the reader reads a float at whole values (the claim is for those). The
  order book only compares and negates them, so a run over any floats has one over whole numbers taking the same
  branches; the laws compare them too. Again an argument, not a check.
- **Risk laws** ("exposure never above the cap"): the engine has no positions or limits; none stated.

## Not done, and what would carry it further

- Other ordered containers onto the same least keys: Rust's `BTreeMap` (`first_key_value`, `pop_first`), Java's
  `TreeMap` (`firstKey`, `pollFirstEntry`), `heapq` (`heappush`, `heappop`, `h[0]`: a multiset, least by the element),
  `sortedcontainers`. Each is a reader's mapping onto `least`; none is new structure.
- Nested collections (a dict of deques by price: krabduke/lob, most C++ and Rust engines): a map keyed by (price, place)
  would need two-part keys in the reader.
- Matching loops over the book (`while qty and book: fill the best`): the loop's pass as a step of its own (the state
  between passes as state) would read them; folds over a carried list (Lane L) do not.
- A step law reading a division needs the kernel to read functions in step laws (a trusted change, Lean first).

## Gates and review

- **Review** (terra, read-only, on the reading of lists): four findings, each fixed and tested (core/ordered.test.ts's
  refusals): a list read through `bool()` saw the list before the step's writes; a call's own arguments (or min's
  `default=`) writing the list before the call read it; `remove` on a dataclass with `eq=False` (identity) read as
  field equality. Also guarded: a choice cell given a string other than its literals.
- **Quick bar** (bf732d8 against ae36917): none wrong in any group; the one solid loss, ITS's elmhes, flips at the 60 s
  limit (the base answers it at 51.8 to 60 s) and is lost the same way in other lanes' bars against ae36917; the
  real-world corpus, both frontier rounds and research/dag's 332 goals unchanged.
- **Suites** (5122df8, with the review's fixes): by default 240 of 240, `--usual` 240 of 240 (the new `trading` job
  among them); rw, f1, f2 unchanged. tsc (no error outside the research files that need the vendored repos) and oxlint
  on the changed files clean.
- **Size:** core/ +28 KB outside tests (extract-step.ts +17 KB, machine.ts +3.5 KB, dsl.ts +3.2 KB, laws.ts +1.6 KB);
  kernel/ and lean-kernel/ unchanged.

# Lane TR (gen/laneTR): rounding in the kinds, while loops over the state's lists, the corpus

The tile's two missing parts: the pieces through the CLI, and the measure on several engines in the readers' languages.

## Rounding to a tick

**In the kinds** (core/dsl.ts, core/ticks.test.ts): `floorTo(k)`, `ceilTo(k)`, `roundTo(k, mode)` and `onTick(k)` on
naturals, `int`s and decimals (a decimal's tick in its own units: `price.roundTo(0.05)` at 2 places is 5 cents), the
modes `'halfEven'` (Python's round), `'halfUp'` (JavaScript's and Java's Math.round), `'halfDown'` and `'halfAway'` (Go's
and Rust's round). Each is built from divBy and modBy (a half up is ⌊(2x + k) / 2k⌋·k, a half down −⌊(k − 2x) / 2k⌋·k, a
half to the even one by the remainder's double against k), so nothing new reaches the kernel or Lean. Tested against a
reference over exact integers at every residue, and a quoter's laws proven (on a tick, at most the price, within a tick,
within half a tick, each mode's own half) with a mode said to round its halves another way refuted.

**In the readers.** The executor's quotient (core/extract-step.ts) takes a mode: floor, ceil, trunc, and to the nearest
by `even`, `up` or `away`, behind one SX node (`rnd`) any reader lowers to. Java: a float division is kept (`fdiv`, a
true division, read only where Math.round, rint, floor, ceil or a cast to an integer rounds it; anywhere else a value
outside the subset, refused where the rule reads it), Kotlin's `round` the even one; an integer passed or cast as a
float (javac's `Math.round(float)` for an integer argument, `(float) p`) is exact below 2^24, an edge past it, and a
division with a float operand has a float's precision. TypeScript: Math.trunc of x / k beside floor and ceil (its
Math.round stays refused: the TypeScript reader keeps no edge, and past 2^52 it isn't exact).

**A fix to gdp-wired's own claim.** laneO read Python's `round(a / k)` as exact below 2^53. It isn't: a / k not a half
is at least 1/(2k) from one, and the float a / k is within |a / k|·2^-53 of a / k, which is below 1/(2k) only for |a| <
2^52. At a = 3·2^51 + 2, a / 3 = 2^51 + 2/3 is stored as 2^51 + 0.5 and Python rounds it to the even 2^51: round(a / 3)·3
− a = −2, while the rule (exact) said +1, so "within half a tick" was proven of code that breaks it there. Every
rounding to the nearest now has an edge at |a| ≥ 2^52 (2^23 for a float's 24 bits, and floor, ceil and trunc at 2^24
for floats): the rule refuses there and the check counts it apart (the shared executor's check now reads the edges, as
Go's did). core/rounding.test.ts replays the case in Python.

**Floats, what stays refused.** A float division read anywhere but under a rounding to a whole number; a division by a
value that isn't a constant (Java's `|p − ref|·100.0 / ref > max`); a float remainder; a non-whole float literal. The
reason is the same each time: the rule's numbers are exact integers, and the code's float operation rounds at a place
that depends on the operands' size, which no linear term states. Where rounding back to an integer makes the result
exact below a bound, the reader reads it with that bound as an edge; elsewhere it refuses rather than approximate.

## While loops over the state's lists

A matching loop (`while left > 0 and self.asks: best = min(self.asks, key=...); fill; take it out`), a scheduler
running what is due (`while self.tasks and self.tasks[0].due <= now: self.tasks.pop(0)`), a window pruning old hits: a
while loop whose passes take the first item of a list of the state, each pass that goes on taking it out. Python's
`while` is now read (core/extract-step.ts `whileStmt`, `whileRank`; core/loops.test.ts) in two ways, both a fold as
laneO's for loops are (every request carries the run its passes compute, assumed to be that run; nothing unrolled):

- **In the list's places** (xs[0], pop(0), xs[-1], pop()): the passes are the places in order (from the last down for
  the other end), each place's pass holding its item; a pass where the condition fails, or a break, return or failure,
  ends the loop; after the loop each place reached is as its pass left it (one write at every key, read from the run
  at the place), and where the passes ran out of items the condition is read once more with the list empty (a loop
  that goes on then never ends: refused there).
- **In an order of its own** (min or max by a key, Mesa's best bid and ask): the request also carries the list's held
  keys in that order (`<list>__ord`, increasing by the order at every two places, each held) and each held key's place
  there (`<list>__rk`, the place's item tying it under the order), and the run holds, for each list, how many items
  the passes took out and the fields of the one they hold; a pass's item is the one at that count. After the loop the
  items placed before the count are out and the one at it has the passes' fields. Several lists at once (Mesa's
  clear_all_crosses takes a bid and an ask each pass).

Two constraints shaped this, and one review. The kernel decides a quantified condition by finitely many keys only where each key is
read as a map's key or compared with a term that doesn't read it (kernel/kernel.ts's `keyOnly`, `apart`): a pass's
item read through the run (`asks.at(ord.at(run.at(i).a).k)`) is in the fragment, but "the least item after the last
taken" over every pass and key is not (it compares two bound keys' cells), nor is "the key at its place is itself"
(`ord.at(rk.at(k)).k = k`, the key against a term reading it). So places are tied to keys through the order's parts,
and two items that tie under the order have no increasing list: the rule refuses there, an edge the check counts apart
(which of two tied items comes first is the code's: Python's list order, a heap's layout). Second, a fold over a dict's
keys in order would run over every number up to the greatest key (a price), which the check's run can't hold: refused.

**Review** (an independent read of the code, terra being unavailable: the OpenAI login pi uses was refused): ten
findings, each fixed and tested. The one that mattered: the places map only tied a key to a place by the order's
parts, so two tied items could share a place and the rule took one pass for both; now two held keys at one place are
one, so ties have no run and the rule refuses there. The others: the order's assumptions held for every request (now
only where the loop runs, and ties an edge only there); a loop's write at every key on one branch kept on the other; a
failure after the loop not seen as following a write; the list read again after a pass took its item out (it gave the
same item); remove's equality and an order field changed before a remove; a pass in a loop over places that keeps its
item now ends the loop (the next condition reads the same item); Java's `Math.round` of an integer division (read as
the exact quotient), an integer converted to a float, and a float operand's precision; TypeScript's Math.round (a
refusal where the code goes on, withdrawn).

Refused, each where it is: a pass that writes the state other than its own item (a counter of the object, another
map, an append to the list), reads another item of the list, or changes a field the order reads of an item it keeps; a
list read in two orders in one loop; and, as the rule's refusal (seen by the check where the code reaches it), a pass
that keeps its item where the condition holds again (the code's next pass would take the same item).

**What it proves.** Laws about each item through the passes' own place: the queue's "the tasks run were due" is proven
in seconds; "no task left is due" is not proven (it isn't true: a due task can wait behind one that isn't; the search
found no run within its budget, so unknown, not broken). In an order of its own, the reading is exact (the drain test:
2,300 requests from the start and drawn states, every branch arm), and "an ask filled never grows" is proven, but at
2 to 4 minutes and 5 to 9 GB; at Mesa's size (two lists, two orders, eight least keys) the prover runs out of memory
(over 10 GB) even with no law, the increasing list over every two places and the places map each adding gigabytes.
Laws that need induction over the passes ("fills never exceed the order": 0 ≤ left ≤ qty at every pass) aren't
proven by any fold: the equations alone don't give a fact of every pass (core/extract-py.test.ts says so of laneO's
folds), and no lemma about a fold's running values is inferred yet.

## The measure: research/trading/corpus

Six engines at pinned commits (`engines/<id>.json`: the repository, the files, the comment laws and gdp.toml's lines,
nothing else written), run through the CLI on boat (`bun research/trading/corpus/run.ts --jobs`, then `--collect`;
results.md). Every engine besides Mesa was found by searching for order books, matching engines and risk modules under
MIT, Apache-2.0, BSD or ISC in the readers' languages, preferring the smallest and flattest.

| Engine | Language | Verdicts | What stops the rest |
| --- | --- | --- | --- |
| mesa (mesa-examples, Apache-2.0) | Python | 3 proven, 2 refuted (each run replayed in the code by research/trading/mesa.ts), 9–12 s a law | |
| mesa-clear (the same, with clear_all_crosses) | Python | read and checked exactly (2,314 requests, every branch arm, ties counted apart); no verdict | the prover runs out of memory (over 10 GB) on two lists taken by orders of their own, even with no law |
| zaranip/trading-system (MIT) | Python | not read | an item class whose fields its `__init__` sets from untyped arguments (no type to read them by); heaps of objects ordered by an `__lt__` that branches on the item's side; one object in the heap and in the index |
| tpmullee/financial-markets-studio (MIT) | Python | not read | `str.lower`; then heaps of `[key, time, id, order]` lists and an index holding the same entries |
| Nicolas-Pedernera/order-matching-engine (MIT) | TypeScript | not read | arrays of records and loops (the TypeScript reader has neither) |
| manuelinfosec/limit-orderbook-go (MIT) | Go | not read | shopspring/decimal prices; `container/heap` through an interface |
| borischeunguk/MicroOptimus RiskManager (Apache-2.0) | Java | not read | an enum of another source root read as a class (`OrderType.LIMIT`); then a double quotient by a field (the price deviation) |

So the measure holds on one engine of six, as laneO left it; the five others are refused, each at the first construct
the readers don't take, never misread. What real engines are made of, from this sample: heaps (`heapq`,
`container/heap`, `BinaryHeap`, `PriorityQueue`) more than sorted maps, holding tuples or objects that an index holds
too; nested levels (a price's queue); floats or decimal libraries for prices; and a matching loop over two sides at
once. Reading them needs heaps whose top ties are an edge, objects in two places of the state, and the loops' proofs at
the scale of a real book, in that order.

**Defects.** Reading the five refused engines found five defects, one in each, each replayed in the project's own
code at its pin (kept private, not contacted). None came from a verdict: each engine was refused before its laws were
read.

## Gates (lane TR)

- **Trusted code:** none changed (kernel/, lean-kernel/, core/check.ts: no diff), so no Lean twin, mutants or kernel
  review were needed. terra (pi, `--provider openai`) was unavailable: the OpenAI login was refused (`invalid_grant`).
  An independent agent reviewed the reader changes instead; its ten findings are above, each fixed.
- **Tests:** the trading job (core/ticks, rounding, ordered, orderbook, loops tests and examples/orderbook.ts) 17 of 17
  and its three examples; `bun scripts/test-shards.ts`, 7 shards on boat, every shard exit 0. One 5 s test,
  infer.test.ts's first, timed out in one shard; on fixed large VMs, four runs a side, it takes 2.5–3.2 s here and
  2.1–7.9 s on main.
- **Quick bar** (`bun bar --quick`, 1d8ed91 against main 811e4ea, every group): wrong 0 in every group, nothing lost
  solid; CHC-COMP −9, ITS −6 and −2 per component, none solid (7 and 6 flips at the time limit; no code those read
  changed); TIP, SV-COMP, both frontier rounds, the real-world corpus and research/dag's 332 unchanged; Lean 6 of 6.
  On the final tree (83556a7 against ae2e91b: f1, f2, rw): wrong 0, nothing lost solid; the real-world corpus's 4 lost
  at the limit (its rules are written by hand: only the methods added to the kinds reach them) were noise: with the
  base launched beside the candidate, 2 gained, 0 lost.
- **tsc** no error outside the research files that need the vendored repos; **oxlint** clean on this lane's files
  (one error remains in research/hw/run-more.ts, not this lane's).
- **Size:** core/ +50 KB outside tests (extract-step.ts +36 KB, extract.ts +4 KB, extract-check.ts +3.3 KB, dsl.ts
  +3 KB).
