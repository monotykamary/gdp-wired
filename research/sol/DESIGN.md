# Smart contracts: Solidity read onto the step IR (gen/laneS)

ROADMAP section 6, step 4: one-threaded state over a ledger is the shape gdp-wired already proves; what it needed was
bit-precise 256-bit arithmetic usable by laws, re-entrancy as an environment, and a Solidity reader. All three are here,
untrusted (no kernel change), each checked against the contract's own bytecode on an EVM.

```
  Solidity ──► solc --standard-json (AST, bytecode, storage layout) ──► core/extract-sol.ts: the AST lowered into the
  step IR ──► core/extract-step.ts (the shared executor) ──► the rule ──► laws (`/// gdp: law`) proven or broken
                                                    │
  anvil (foundry) ◄── core/sol/harness.py (JSON-RPC, stdlib) ◄── the check: every request, state, cell, result, revert
                  ◄── Agents and a Director (core/sol/Replay.sol) ◄── re-entrant runs, and every broken law's run
```

## The pieces

| Piece | Where | What it does |
| --- | --- | --- |
| The reader | `core/extract-sol.ts` (`gdp-wired/extract-sol`, `extractSolidity`) | solc's compact AST lowered into the IR in TypeScript (Go's lowering is the model): the contract's linearized bases, its state, its external functions with their modifiers, internal and virtual calls inlined (`super` along the linearization), constructors base first with the arguments given to them |
| The harness | `core/sol/harness.py` | anvil over JSON-RPC: deploy (the same solc's bytecode), set a state (the code copied to a fresh address, storage written slot by slot, mapping slots by keccak), read it, call with msg.sender impersonated and msg.value sent, eth_call for the result then the transaction |
| The width | `core/extract-step.ts` (`IntTy.mod`, `pastMod`, `wrap`) | uint256 at a symbolic 2^256 (below) |
| Several keys a step | `core/extract-step.ts` (`writeCell`, `padWrites`), `core/extract.ts` | a transfer writes two cells of one map; printed as `M.each(k$ => ...)` |
| Re-entrancy | `core/extract-sol.ts` (`split`, `replayer`), `core/sol/Replay.sol` | a call into other code as two steps with any steps between (below) |
| `sum(m)` | `core/laws.ts` | a map's cells summed, in a comment law (`sum(balances) == totalSupply`) |
| The CLI | `core/cli.ts` | `.sol` files; a broken law's run replayed on the code before it is shown broken (`Extraction.replay`) |

## 256 bits without a constant past 2^53

The kernel refuses any coefficient past 2^53, so 2^256 can't be a literal. It is a variable instead: `W256$`, a field
of the state the constructor sets from a param and no step writes, with the precondition W > every constant the code
reads (at least 2). An unsigned 256-bit value is a natural below W (a range law, `x < W256$`, beside the rule's
invariants; a request's argument at or past W is no request). Checked arithmetic reverts where `a + b >= W` or
`a - b < 0` (and a product `a * b >= W`, degree 2); unchecked arithmetic wraps by cases: a sum or difference of two
values below W is past it at most once (`ite(e < 0, e + W, ite(e >= W, e - W, e))`); a product wrapped is refused.
`type(uint256).max` is `W - 1`.

**Why it is sound.** The rule is a family, one machine per W. A law proven for the family is proven for every W the
precondition allows, 2^256 among them, and the machine at W = 2^256 is the code's (the check compares them). A broken
law is the other way round: a run may break it only at a narrow W (a sum past 7 that 2^256 holds). So every broken law's
run is replayed: the rule at W = 2^52 from the same requests, then the code on anvil; it is shown broken only where both
break it, else unknown ("a run breaks it in the rule, not on the code").

**The check at a width it can run.** The rule's numbers stop at 2^53, the code's at 2^256. The check fixes W at 2^52
(the param's draw, `derived`; the prover's witnesses keep theirs, refused below 2^40) and maps values by two bands: v
below ceil(W/2) is v, any other is 2^256 - (W - v). Sums, differences, order and overflow agree wherever no result lands
between the bands (W - 1 and 2^256 - 1 overflow alike: a draw near W, the params' ±1, exercises the wrap). A value of the
code between the bands is outside what the check compares. The contract's ether is a uint256 too (the same bands); no
request brings ether past W (none exists).

## Addresses, mappings, msg

Addresses are naturals compared only by equality (ordering them is refused), address(0) is 0, no request comes from it:
the code is symmetric in them. A mapping's cell is held where it isn't zero (Solidity's storage: a zero written is no
cell). msg.sender is an input of every request, msg.value of a payable one, block.timestamp the request's time.

A mapping of mappings (ERC-20's allowances) is not in the rule's state: each cell read is any value of its type, an input
of the request (one a step: a second read in one step is refused, so two reads are never made one), and its writes are
left out. That is more runs than the code has, so a law proven holds of the code, and a law can't read such a map. The
check sets every cell of the addresses the object has seen to the request's value before a method that reads it. (Keyed
by one number, a·2^19 + b, the map was exact, but the kernel took minutes on a step reading it where a map keyed by
one address took 3 s: research/sol/pilot/Allow1.sol, Allow2.sol.)

Two writes of one map in a step (a transfer's two cells) are printed as `M.each(k$ => ...)`, a write at every key. The
rule's compiled runtime wrote one densely up to its last breakpoint (a million keys at most); it now follows the
interpreter's stretches (core/machine.ts `$dense`: each breakpoint and one key of each stretch between, a stretch filled
only where its value differs from the one past the last), so a key of 2^32 costs what a key of 3 does.

## Re-entrancy: the environment that calls back

A value sent to an address (`a.call{value: v}("")`, `send`, `transfer`) is a call into other code. With the plain
reading the callee is an account without code; the rule the laws are proven of (the default, `reentrant: false` to
turn it off) makes it any code: the entry is split at its call into two steps.

- `withdraw`: up to the call. Where the contract holds less than the value, the call fails at once and the rest runs
  (no code ran). Else the value moves, `pending$` goes up by one and the call's locals are kept in `frames$withdraw` at
  that depth; the step ends.
- `withdraw$resume`: the frame on top given back (none: no request; the last call returns first, as the EVM's), `ok`
  an input (the callee returned or reverted: a revert gives the value back), then the rest of the function.

Between the two, any step of the rule may run, by any address: the callee calling back, or calling others who call
back. A law about the state is about the states between transactions: it reads `pending$ == 0 implies <law>`
(`Extraction.quiet`, core/laws.ts). The model has every run the code has (a revert inside a callee keeps, in the rule,
what the callee's own calls did: more runs, so a proof still holds; a refutation is replayed).

**Checked against the code with real re-entrancy.** core/sol/Replay.sol: an `Agent` at every address a run names (the
code set there with anvil_setCode) and one `Director` holding the run's script. A run of the rule is cut into the code's
transactions (from a call at depth 0 to depth 0 again); each transaction is one call of the Director, which makes the
first call by its Agent; when the contract sends an Agent a value, the Agent asks the Director for the script's next
calls and makes them from inside, up to the return (`ok`), then returns or reverts. After each transaction the code's
state is compared with the rule's, and every call of the script must have succeeded. The extraction's own check replays
the rule's random runs (40 by default, each up to 12 steps with every pending call returned); the CLI replays every run
that breaks a law.

**The check's probes.** A step's refusal condition holds at no step the rule takes, so its probe (refute "it never
holds") is a proof; on ERC20Mock one such proof ran past 8 minutes. The Solidity front end probes the branches'
conditions only (`check.probes: 'writes'`, core/extract-check.ts), 30 of them there, each answered in milliseconds.

## Measured

(filled below by the runs)

## Not yet

- Loops, arrays, strings and bytes (their state left out where no step reads it), structs other than a mapping's
  value, inline assembly, try/catch, calls of other contracts (an interface's function: a call into other code that
  returns data), `this.f()`, immutables, signed and unsigned widths between 49 and 255 bits, constants past 2^53
  (`1e18`): each refused where it is read, with why.
- A call into other code inside a branch, or inside an internal function: refused in the re-entrant reading (the split is
  at the top of an entry's body after its modifiers).
- Branch coverage (anvil runs the bytecode: the arms aren't counted).
- `stores`, `answers`: a contract has no other code it reads but through calls, which are refused.
