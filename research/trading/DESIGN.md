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
