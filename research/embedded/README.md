# Safety-critical, embedded: the supervisory logic of real firmware

ROADMAP.md section 4 puts gdp-wired's place in safety-critical code at the discrete supervisory logic: modes,
interlocks, alarms, arming checks, watchdogs. Continuous control laws are KeYmaera X's (hybrid systems), and
qualification under DO-178C or ISO 26262 is mostly not technical; both stay out. This note is the lane's measure:
real open-source firmware in C and C++, read as it ships by `gdp-wired check`, its supervisory laws stated as
`gdp: law` comments, each decided, each refuted one run again on the real code.

    bun research/embedded/corpus/run.ts [--only <id>] [--ms 60000] [--json out] [--md out]   # the corpus (clang needed)
    bun research/embedded/corpus/run.ts --jobs > jobs.json                                   # one boat job an item
    bun research/embedded/corpus/run.ts --score <runs dir> --md results.md --json results.json
    bun research/embedded/repro/run.ts                                                       # the refuted laws' runs

## The corpus (corpus/items.ts)

| Item | Project, licence | Domain | What is read |
| --- | --- | --- | --- |
| makair-alarm | MakAir ventilator firmware, Unlicense | medical | one alarm's detection count and trigger |
| makair-activation | MakAir | medical | start and stop: a running ventilator stops on a second press within 5 s |
| makair-rpi-watchdog | MakAir | medical | the display computer's watchdog: power cut after 60 updates without a heartbeat |
| px4-arming | PX4 Autopilot v1.14.3, BSD-3-Clause | flight control | the commander's arming state machine: its table, the preflight checks |
| canopen-nmt | CANopenNode (9b8beed), Apache-2.0 | industrial fieldbus | NMT (CiA 301): boot, commands, the error behaviour leaving operational |
| canopen-node-guarding | CANopenNode | industrial fieldbus | life guarding: a guard request rearms; without one, the timeout |
| foxbms-interlock | foxBMS 2 v1.12.0, BSD-3-Clause | automotive BMS | the interlock driver's state machine, its re-entrance guard and timer |

Each item names its repository, commit and files; the runner fetches them (nothing is vendored), inserts the laws
where a reviewer would put them and writes the item's gdp.toml (the modelling choices, each with its reason). The
shims (`corpus/shims/`) stand in for what a board or a build makes (a HAL register header, FreeRTOS's handle types,
PX4's generated uORB topics) and for another module the code calls (PX4's arming checks, whose verdict is the
request's): declarations only.

## Results

See `corpus/results.md` (the boat run, 60 s a law). The refuted laws, each run again on the real code by
`repro/run.ts` (output in results.md):

- **px4-arming `shutdown_is_final`:** the transition table keeps SHUTDOWN, but in HIL a request for STANDBY is always
  valid ("HIL can always go to standby"), from SHUTDOWN too. By design in HIL; the law with HIL excepted is proven.
- **px4-arming `denied_changes_nothing`:** in HIL, STANDBY_ERROR is cleared to STANDBY before the request is judged,
  so a denied request still changes the state. By design ("recover from a prearm fail"), not in the table.
- **makair-alarm `first_detection_counts`:** a detection at cycle 4294967295 right after a reset is taken as already
  counted (the sentinel UINT32_MAX). Not reachable in practice (2^32 breaths).
- **canopen-node-guarding `disable_clears_the_timeout`:** disabling the slave (a heartbeat producer configured) stops
  the life timer but keeps a raised timeout, and its error bit, until a guard request that no longer comes. A
  candidate defect, kept private until its intent is clear.

One law is open: makair-alarm `cycles_counted_only_when_triggered` is false at a threshold of 255 (the uint8_t count
wraps past it, 256 detections deep, beyond the search's runs; the repro shows the wrap); MakAir's thresholds are 1 to 3.

## What the C and C++ readers gained (general, each with tests in core/extract-c.test.ts)

- **State in globals.** A file that keeps its state in globals (foxBMS's `static ILCK_STATE_s ilck_state`) is one
  object: its stem the entry (inferred where no struct is), each global a field, every function a method, the
  non-static ones (or `methods`) its requests, each global's initializer its start. A global the file only reads and
  doesn't own (extern, volatile, or not static: a register, another task's value) is the request's. `leave` names
  globals or fields that are an output for other code (a database mirror, a CAN buffer), never read into the rule.
- **Bit operations.** `& | ^ ~ &^` with a constant (a flag set, cleared, tested, toggled; a mask) are exact in linear
  terms in every reader's executor, each run of a mask's ones `((x div 2^lo) mod 2^n)·2^lo`; a chain of them on one
  value composes into one form `(x & A) ^ B`, so a bit of the result is a bit of x. Two values of 16 bits or fewer are
  read bit by bit. Laws read `x & K` and `x | K`, hex and binary literals; a law of one step through keys naming each
  run (the kernel's step laws read no function). Two wider values are refused (bit-vectors).
- **Embedded idioms.** A side effect inside an expression (`if (--timer > 0)`) runs before its statement; `do { }
  while (0)` once; an endless loop (an assertion's trap) is the step's failure, the check's harness timing each call;
  a `void *` set to NULL or not and tested against NULL is a flag (CANopen's CO_FLAG); a constant table (`static
  constexpr bool arming_transitions[6][6]`) is read by cases, an index past it the step's failure; a C++ reference to
  a struct is the caller's object; answers are per constant arguments (`CO_isError(em, BUS_OFF)`); `cut` answers the
  file's own getter of another object's state.
- **Floats are left out, not read.** A float value is opaque, a float field written as the code writes it and never
  compared; a float read into an integer, a condition or a comparison is refused there (foxBMS's interlock scales its
  voltages in floats; no law reads them).
- **Fixes found on the way.** An unnamed enum's typedef (clang 21's spelling) recursed forever; a for's absent parts
  crashed the comment filter; a merge lost that one of its two paths' conditions holds, so a branch that writes and
  then returns left later refusals unconditioned (over-refused; the check caught it); C++ other code couldn't be
  stubbed (the linkers' demangled names: now matched through nm and c++filt); a C++ enum without a fixed type is its
  enumerators' bit-field range (another value undefined to make, which crashed the harness).

## What stays out, and why

- Floats in what the rule keeps (control laws: KeYmaera X's), inline assembly, pointer arithmetic beyond indices of
  fixed arrays, function pointers (callbacks), loops other than an endless trap, bit operations of two values wider
  than 16 bits. Two candidates were left out of the corpus for these, by reading their code: MakAir's AlarmController
  (loops over an array of Alarm objects, its snooze timing among them) and foxBMS's sys_mon (a loop over its tasks
  and a callback through a function pointer). Bounded loops over fixed arrays, unrolled, are the next reader step.
- A file's laws over several files' state (PX4IO's mixer writes registers another file defines through another
  file's functions): refused at the call, which is given the rule's state.
