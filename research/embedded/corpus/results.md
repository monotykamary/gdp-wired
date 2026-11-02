# The embedded corpus: boat, 60 s a law, commit efad281 (corpus3; repro.log beside it)

23 laws on 6 files of 4 projects: 18 proven, 4 broken, 1 unknown, 0 not read; wrong 0

With canopen-nmt (runs/embedded/boat/nmt2, each law alone): 28 laws on 7 files, 18 proven, 4 broken, 6 unknown; wrong 0.
canopen-nmt is read and checked against its code (319 requests from the start, 400 from drawn states, 3 s), but its
five laws are unknown: the prover's budget runs out at 539 hypotheses (the step's bit tests, the error register
masked by NMTcontrol bit by bit, the heartbeat timer), and each law ran 20 to 30 minutes, past its --ms 20000.

| Item | Domain | Law | Expected | Verdict | Time |
| --- | --- | --- | --- | --- | --- |
| makair-alarm | medical | detections_capped | proven | proven | 0.7 s |
| makair-alarm | medical | cycles_counted_only_when_triggered | unknown | unknown | 60.4 s |
| makair-alarm | medical | same_cycle_counts_once | proven | proven | 0.5 s |
| makair-alarm | medical | first_detection_counts | broken | broken | 0.4 s |
| makair-activation | medical | stop_needs_a_second_press | proven | proven | 0.3 s |
| makair-activation | medical | refresh_never_stops | proven | proven | 0.1 s |
| makair-rpi-watchdog | medical | countdown_at_most_its_start | proven | proven | 0.2 s |
| makair-rpi-watchdog | medical | switched_off_when_count_ends | proven | proven | 0.2 s |
| px4-arming | flight control | armed_only_when_checks_pass | proven | proven | 6.3 s |
| px4-arming | flight control | armed_only_from_standby | proven | proven | 1.9 s |
| px4-arming | flight control | shutdown_is_final | broken | broken | 0.7 s |
| px4-arming | flight control | shutdown_left_only_in_hil | proven | proven | 1.4 s |
| px4-arming | flight control | denied_changes_nothing | broken | broken | 0.0 s |
| canopen-node-guarding | industrial fieldbus | timeout_when_life_expires | proven | proven | 0.6 s |
| canopen-node-guarding | industrial fieldbus | guard_request_rearms | proven | proven | 0.3 s |
| canopen-node-guarding | industrial fieldbus | life_timer_counts_down | proven | proven | 0.3 s |
| canopen-node-guarding | industrial fieldbus | disable_stops_guarding | proven | proven | 0.3 s |
| canopen-node-guarding | industrial fieldbus | disable_clears_the_timeout | broken | broken | 3.4 s |
| foxbms-interlock | automotive BMS | init_accepted_only_when_uninitialized | proven | proven | 4.2 s |
| foxbms-interlock | automotive BMS | never_uninitialized_again | proven | proven | 1.6 s |
| foxbms-interlock | automotive BMS | reentry_guard_released | proven | proven | 3.3 s |
| foxbms-interlock | automotive BMS | no_illegal_request_counted | proven | proven | 3.7 s |
| foxbms-interlock | automotive BMS | timer_bounded | proven | proven | 3.4 s |

## The refuted laws run on the real code (research/embedded/repro/run.ts, boat)

```
== makair-alarm (makers-for-life/makair-firmware @ 042ad55e910953c0f13c5be0a26ae468253c0059)
first_detection_counts: threshold 1, detected(4294967295) right after construction: triggered=0 (the law says 1)
threshold 255, 255 detections: triggered=1
cycles_counted_only_when_triggered: the 256th detection: triggered=0, cycles since trigger=0 (the count wrapped to 0)
== px4-arming (PX4/PX4-Autopilot @ v1.14.3)
shutdown_is_final: HIL on, from SHUTDOWN, request STANDBY: result=1 state=1 (SHUTDOWN is 4)
denied_changes_nothing: HIL on, from STANDBY_ERROR (3), request ARMED: result=-1 (DENIED is -1) state=1
== canopen-node-guarding (CANopenNode/CANopenNode @ 9b8beed8367241e96ac03f916cd5a500bcb2cf23)
a guard request: lifeTimer=1000 timeout=0
  CO_error(set, bit 27, code 0x8130)
1000 us without one: lifeTimer=0 timeout=1
disable_clears_the_timeout: the slave disabled: lifeTimer=0 timeout=1 (the law says 0)
```
