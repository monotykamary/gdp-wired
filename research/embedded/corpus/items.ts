// The embedded corpus: real open-source firmware's supervisory logic (modes, interlocks, alarms, arming checks,
// watchdogs), each file read as it ships by `gdp-wired check` (the CLI, the C and C++ readers), its laws stated as
// `gdp: law` comments where a reviewer would put them. Nothing here is the code: each item names its repository, the
// commit, the files fetched and where each law goes; research/embedded/corpus/run.ts fetches the files, inserts the
// laws, writes the item's gdp.toml beside the file and runs the CLI. The shims (shims/<project>/) stand in for what a
// board or a build generates (a HAL's register header, an RTOS's handle types, PX4's uORB topics) or for another
// module the code calls (PX4's arming checks): declarations only, their values the request's.
//
// `expect` is what the law is believed to be: proven (true), broken (false, with the run the code takes), unknown.

export type Law = {file: string, before: string, law: string, expect: 'proven' | 'broken' | 'unknown', note?: string}
export type Item = {
  id: string, project: string, domain: 'medical' | 'flight control' | 'industrial fieldbus' | 'automotive BMS', repo: string, commit: string,
  licence: string, author: string, files: string[], target: string, shims?: string,
  // (files written over a fetched one: a stand-in at the path the code includes; or made from a fetched one)
  overlays?: Record<string, string>, derive?: Record<string, {from: string, drop: RegExp}>,
  // gdp.toml beside the target: {repo} is the fetched tree, {shim} the item's shims
  toml: string, laws: Law[], what: string,
}

const L = (file: string, before: string, expect: Law['expect'], law: string, note?: string): Law => ({file, before, law, expect, ...(note ? {note} : {})})

export const ITEMS: Item[] = [
  // --- MakAir (a ventilator built in 2020; firmware public domain) ---------------------------------------------------------
  {
    id: 'makair-alarm', project: 'MakAir ventilator firmware', domain: 'medical', repo: 'makers-for-life/makair-firmware', commit: '042ad55e910953c0f13c5be0a26ae468253c0059',
    licence: 'Unlicense (public domain)', author: 'Makers for Life', files: ['srcs/alarm.cpp', 'includes/alarm.h'], target: 'srcs/alarm.cpp', shims: 'makair',
    what: 'one alarm: detections counted once per breathing cycle up to its threshold, then triggered; reset when not detected',
    toml: 'flags = ["-I{shim}"]', laws: [
      L('srcs/alarm.cpp', 'Alarm::Alarm(', 'proven', 'detections_capped: m_detectionNumber <= m_detectionThreshold'),
      L('srcs/alarm.cpp', 'Alarm::Alarm(', 'unknown', 'cycles_counted_only_when_triggered: m_cyclesSinceTrigger == 0 or m_detectionNumber == m_detectionThreshold',
        'false at a threshold of 255 (the uint8_t count wraps past it), 256 detections deep; MakAir sets thresholds of 1 to 3'),
      L('srcs/alarm.cpp', 'void Alarm::detected(', 'proven', 'same_cycle_counts_once: p_cycleNumber == old(m_cycleNumber) implies m_detectionNumber == old(m_detectionNumber)'),
      L('srcs/alarm.cpp', 'void Alarm::detected(', 'broken', 'first_detection_counts: old(m_detectionNumber) == 0 and m_detectionThreshold > 0 implies m_detectionNumber == 1',
        'a detection at cycle 4294967295 right after a reset is taken for one already counted (the sentinel UINT32_MAX)'),
    ],
  },
  {
    id: 'makair-activation', project: 'MakAir ventilator firmware', domain: 'medical', repo: 'makers-for-life/makair-firmware', commit: '042ad55e910953c0f13c5be0a26ae468253c0059',
    licence: 'Unlicense (public domain)', author: 'Makers for Life', files: ['srcs/activation.cpp', 'includes/activation.h', 'includes/buzzer.h'], target: 'srcs/activation.cpp', shims: 'makair',
    what: 'start and stop: a running ventilator stops only on a second press of stop within 5 s',
    toml: 'flags = ["-I{shim}"]', laws: [
      L('srcs/activation.cpp', 'void ActivationController::onStopButton()', 'proven', 'stop_needs_a_second_press: m_state == STOPPED implies old(m_state) == STOPPED or old(m_state) == RUNNING_READY_TO_STOP'),
      L('srcs/activation.cpp', 'void ActivationController::refreshState()', 'proven', 'refresh_never_stops: m_state == STOPPED implies old(m_state) == STOPPED'),
    ],
  },
  {
    id: 'makair-rpi-watchdog', project: 'MakAir ventilator firmware', domain: 'medical', repo: 'makers-for-life/makair-firmware', commit: '042ad55e910953c0f13c5be0a26ae468253c0059',
    licence: 'Unlicense (public domain)', author: 'Makers for Life', files: ['srcs/rpi_watchdog.cpp', 'includes/rpi_watchdog.h', 'includes/parameters.h', 'includes/config.h'], target: 'srcs/rpi_watchdog.cpp', shims: 'makair',
    what: 'the display computer\'s watchdog: without a heartbeat for 60 updates its power is cut, then restored',
    toml: 'flags = ["-I{shim}"]', laws: [
      L('srcs/rpi_watchdog.cpp', 'RpiWatchdog::RpiWatchdog()', 'proven', 'countdown_at_most_its_start: m_countDown <= COUNTDOWN_IN_S'),
      L('srcs/rpi_watchdog.cpp', 'void RpiWatchdog::update()', 'proven', 'switched_off_when_count_ends: old(m_rpiWatchdogStep) == COUNT_DOWN and old(m_countDown) <= 1 implies m_rpiWatchdogStep == SWITCH_OFF_RASPBERRY'),
    ],
  },
  // --- PX4 (flight control; BSD-3-Clause) -----------------------------------------------------------------------------
  {
    id: 'px4-arming', project: 'PX4 Autopilot v1.14.3', domain: 'flight control', repo: 'PX4/PX4-Autopilot', commit: 'v1.14.3',
    licence: 'BSD-3-Clause', author: 'PX4 Development Team', files: ['src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', 'src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.hpp'],
    target: 'src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', shims: 'px4',
    overlays: {'src/modules/commander/HealthAndArmingChecks/HealthAndArmingChecks.hpp': 'HealthAndArmingChecks.hpp'},
    what: 'the commander\'s arming state machine: transitions along its table, arming only past the preflight checks (HIL aside)',
    toml: 'flags = ["-std=c++17", "-I{shim}"]\n# the arming transition and the commander\'s forced state; the state\'s name (a string, for messages) left out\nmethods = ["arming_state_transition", "forceArmState"]', laws: [
      L('src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', 'transition_result_t ArmStateMachine::arming_state_transition(', 'proven',
        'armed_only_when_checks_pass: _arm_state != vehicle_status_s::ARMING_STATE_ARMED or old(_arm_state) == vehicle_status_s::ARMING_STATE_ARMED or canArm(...) or not fRunPreArmChecks or status.hil_state == vehicle_status_s::HIL_STATE_ON or old(_arm_state) == vehicle_status_s::ARMING_STATE_IN_AIR_RESTORE'),
      L('src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', 'transition_result_t ArmStateMachine::arming_state_transition(', 'proven',
        'armed_only_from_standby: _arm_state != vehicle_status_s::ARMING_STATE_ARMED or old(_arm_state) == vehicle_status_s::ARMING_STATE_ARMED or old(_arm_state) == vehicle_status_s::ARMING_STATE_STANDBY or old(_arm_state) == vehicle_status_s::ARMING_STATE_IN_AIR_RESTORE'),
      L('src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', 'transition_result_t ArmStateMachine::arming_state_transition(', 'broken',
        'shutdown_is_final: old(_arm_state) != vehicle_status_s::ARMING_STATE_SHUTDOWN or _arm_state == vehicle_status_s::ARMING_STATE_SHUTDOWN',
        'the table keeps SHUTDOWN; in HIL a request for STANDBY is always valid ("HIL can always go to standby"), from SHUTDOWN too'),
      L('src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', 'transition_result_t ArmStateMachine::arming_state_transition(', 'proven',
        'shutdown_left_only_in_hil: old(_arm_state) != vehicle_status_s::ARMING_STATE_SHUTDOWN or _arm_state == vehicle_status_s::ARMING_STATE_SHUTDOWN or status.hil_state == vehicle_status_s::HIL_STATE_ON'),
      L('src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp', 'transition_result_t ArmStateMachine::arming_state_transition(', 'broken',
        'denied_changes_nothing: result != TRANSITION_DENIED or _arm_state == old(_arm_state)',
        'in HIL, STANDBY_ERROR is cleared to STANDBY before the request is judged: a denied request still changes the state'),
    ],
  },
  // --- CANopenNode (an industrial fieldbus stack; Apache-2.0) ----------------------------------------------------------
  {
    id: 'canopen-nmt', project: 'CANopenNode', domain: 'industrial fieldbus', repo: 'CANopenNode/CANopenNode', commit: '9b8beed8367241e96ac03f916cd5a500bcb2cf23',
    licence: 'Apache-2.0', author: 'Janez Paternoster and contributors', files: ['301/CO_NMT_Heartbeat.c', '301/CO_NMT_Heartbeat.h', '301/CO_Emergency.h', '301/CO_ODinterface.h', '301/CO_config.h', '301/CO_driver.h', 'example/CO_driver_target.h'],
    target: '301/CO_NMT_Heartbeat.c', what: 'the network management state machine (CiA 301): boot, commands, and the error behaviour that leaves operational',
    toml: 'entry = "CO_NMT_t"\nflags = ["-I{repo}", "-I{repo}/example"]\n[rules.CO_NMT_t]\n# the node\'s configuration (NMTcontrol, the heartbeat period) is CO_NMT_init\'s: the laws hold of a step from any state\nfrom = "any"\nmethods = ["CO_NMT_process", "CO_NMT_sendInternalCommand"]\n# the heartbeat frame is written for the CAN driver and sent by it\nleave = ["HB_TXbuff", "HB_CANdevTx"]\n# the emergency object\'s error bits, another object\'s: the request\'s\ncut = ["CO_isError", "CO_getErrorRegister"]',
    laws: [
      L('301/CO_NMT_Heartbeat.c', 'CO_NMT_reset_cmd_t\nCO_NMT_process(', 'proven', 'never_back_to_initializing: old(NMT->operatingState) == CO_NMT_INITIALIZING or NMT->operatingState != CO_NMT_INITIALIZING'),
      L('301/CO_NMT_Heartbeat.c', 'CO_NMT_reset_cmd_t\nCO_NMT_process(', 'proven', 'boot_ends_in_a_running_state: old(NMT->operatingState) != CO_NMT_INITIALIZING or NMT->operatingState == CO_NMT_PRE_OPERATIONAL or NMT->operatingState == CO_NMT_OPERATIONAL or NMT->operatingState == CO_NMT_STOPPED'),
      L('301/CO_NMT_Heartbeat.c', 'CO_NMT_reset_cmd_t\nCO_NMT_process(', 'proven', 'bus_off_leaves_operational: (NMT->NMTcontrol & CO_NMT_ERR_ON_BUSOFF_HB) == 0 or CO_isError(NMT->em, CO_EM_CAN_TX_BUS_OFF) == 0 or NMT->operatingState != CO_NMT_OPERATIONAL'),
      L('301/CO_NMT_Heartbeat.c', 'CO_NMT_reset_cmd_t\nCO_NMT_process(', 'proven', 'bus_off_stops_when_configured: old(NMT->operatingState) != CO_NMT_OPERATIONAL or old(NMT->internalCommand) != CO_NMT_NO_COMMAND or (NMT->NMTcontrol & CO_NMT_ERR_ON_BUSOFF_HB) == 0 or CO_isError(NMT->em, CO_EM_CAN_TX_BUS_OFF) == 0 or (NMT->NMTcontrol & CO_NMT_ERR_TO_STOPPED) == 0 or NMT->operatingState == CO_NMT_STOPPED'),
      L('301/CO_NMT_Heartbeat.c', 'CO_NMT_reset_cmd_t\nCO_NMT_process(', 'proven', 'heartbeat_timer_within_period: old(NMT->HBproducerTimer) > NMT->HBproducerTime_us or NMT->HBproducerTimer <= NMT->HBproducerTime_us'),
    ],
  },
  {
    id: 'canopen-node-guarding', project: 'CANopenNode', domain: 'industrial fieldbus', repo: 'CANopenNode/CANopenNode', commit: '9b8beed8367241e96ac03f916cd5a500bcb2cf23',
    licence: 'Apache-2.0', author: 'Janez Paternoster and contributors', files: ['301/CO_Node_Guarding.c', '301/CO_Node_Guarding.h', '301/CO_NMT_Heartbeat.h', '301/CO_Emergency.h', '301/CO_ODinterface.h', '301/CO_config.h', '301/CO_driver.h', 'example/CO_driver_target.h'],
    target: '301/CO_Node_Guarding.c', what: 'the node guarding slave\'s life guarding: a guard request rearms the life timer; without one for the life time, the error',
    toml: 'entry = "CO_nodeGuardingSlave_t"\nflags = ["-I{repo}", "-I{repo}/example", "-DCO_CONFIG_NODE_GUARDING=0x01"]\n[rules.CO_nodeGuardingSlave_t]\n# the guard and life times are CO_nodeGuardingSlave_init\'s (the object dictionary\'s): the laws hold of a step from any state\nfrom = "any"\nmethods = ["CO_nodeGuardingSlave_process"]\n# the guarding response frame is written for the CAN driver and sent by it\nleave = ["CANtxBuff", "CANdevTx"]',
    laws: [
      L('301/CO_Node_Guarding.c', 'void\nCO_nodeGuardingSlave_process(', 'proven', 'timeout_when_life_expires: old(ngs->CANrxNew) or slaveDisable != 0 or old(ngs->lifeTimer) == 0 or timeDifference_us < old(ngs->lifeTimer) or ngs->lifeTimeTimeout != 0'),
      L('301/CO_Node_Guarding.c', 'void\nCO_nodeGuardingSlave_process(', 'proven', 'guard_request_rearms: not old(ngs->CANrxNew) or slaveDisable != 0 or (ngs->lifeTimer == ngs->lifeTime_us and ngs->lifeTimeTimeout == 0 and not ngs->CANrxNew)'),
      L('301/CO_Node_Guarding.c', 'void\nCO_nodeGuardingSlave_process(', 'proven', 'life_timer_counts_down: old(ngs->CANrxNew) or slaveDisable != 0 or old(ngs->lifeTimer) <= timeDifference_us or ngs->lifeTimer == old(ngs->lifeTimer) - timeDifference_us'),
      L('301/CO_Node_Guarding.c', 'void\nCO_nodeGuardingSlave_process(', 'proven', 'disable_stops_guarding: slaveDisable == 0 or (ngs->lifeTimer == 0 and not ngs->CANrxNew)'),
      L('301/CO_Node_Guarding.c', 'void\nCO_nodeGuardingSlave_process(', 'broken', 'disable_clears_the_timeout: slaveDisable == 0 or ngs->lifeTimeTimeout == 0',
        'disabling the slave stops the timer but keeps a life guarding timeout raised (its error bit is reset only when a guard request arrives)'),
    ],
  },
  // --- foxBMS 2 (an automotive battery management system; BSD-3-Clause) ------------------------------------------------
  {
    id: 'foxbms-interlock', project: 'foxBMS 2 v1.12.0', domain: 'automotive BMS', repo: 'foxBMS/foxbms-2', commit: 'v1.12.0',
    licence: 'BSD-3-Clause', author: 'Fraunhofer IISB', target: 'src/app/driver/interlock/interlock.c', shims: 'foxbms',
    files: ['src/app/driver/interlock/interlock.c', 'src/app/driver/interlock/interlock.h', 'src/app/driver/config/interlock_cfg.h', 'src/app/driver/io/io.h', 'src/app/engine/database/database.h',
      'src/app/engine/database/database_helper.h', 'src/app/engine/config/database_cfg.h', 'src/app/engine/diag/diag.h', 'src/app/engine/config/diag_cfg.h', 'src/app/task/os/os.h', 'src/app/main/include/fassert.h',
      'src/app/main/include/fstd_types.h', 'src/app/main/include/general.h', 'src/app/driver/mcu/mcu.h', 'src/app/application/config/battery_system_cfg_types.h', 'src/app/application/config/bms-slave_cfg.h',
      'tests/unit/support/foxbms_config_rtos.h', 'tests/unit/app/application/config/battery_cell_cfg.h', 'tests/unit/app/application/config/battery_system_cfg.h', 'tools/cmock/vendor/c_exception/lib/CException.h'],
    // (the unit tests' battery configuration, its string enum the types header's: what the host build combines)
    derive: {'.gdp-shim/battery_system_cfg.h': {from: 'tests/unit/app/application/config/battery_system_cfg.h', drop: /#if[^\n]*TEST_BS_NR_OF_STRINGS[^\n]*\n(?:.*\n)*?#endif \/\* TEST_BS_NR_OF_STRINGS \*\/\n/}},
    what: 'the interlock driver\'s state machine: initialization only from uninitialized, a re-entrance guard, its timer',
    toml: [
      'flags = ["-DFOXBMS_RTOS_FREERTOS", "-I{shim}", "-I{repo}/.gdp-shim", "-I{repo}/src/app/driver/interlock", "-I{repo}/src/app/driver/config", "-I{repo}/src/app/driver/io", "-I{repo}/src/app/engine/database", "-I{repo}/src/app/engine/config", "-I{repo}/src/app/engine/diag", "-I{repo}/src/app/task/os", "-I{repo}/src/app/main/include", "-I{repo}/src/app/driver/mcu", "-I{repo}/src/app/application/config", "-I{repo}/tests/unit/support", "-I{repo}/tests/unit/app/application/config", "-I{repo}/tools/cmock/vendor/c_exception/lib", "-D__curpc()=0u"]',
      'root = "{repo}"',
      '# a FAS_ASSERT trap stops the controller until the watchdog resets it: no later request sees what the trapped one wrote',
      'onError = "discard"',
      '# the interlock feedback data block: written here for the database (DATA_WRITE_DATA also stamps its header), read by no logic of this file',
      'leave = ["ilck_tableFeedback"]'].join('\n'),
    laws: [
      L('src/app/driver/interlock/interlock.c', 'ILCK_RETURN_TYPE_e ILCK_SetStateRequest(ILCK_STATE_REQUEST_e statereq) {', 'proven', 'init_accepted_only_when_uninitialized: result != ILCK_OK or (old(ilck_state.state) == ILCK_STATEMACHINE_UNINITIALIZED and old(ilck_state.statereq) == ILCK_STATE_NO_REQUEST)'),
      L('src/app/driver/interlock/interlock.c', 'void ILCK_Trigger(void) {', 'proven', 'never_uninitialized_again: old(ilck_state.state) == ILCK_STATEMACHINE_UNINITIALIZED or ilck_state.state != ILCK_STATEMACHINE_UNINITIALIZED'),
      L('src/app/driver/interlock/interlock.c', 'void ILCK_Trigger(void) {', 'proven', 'reentry_guard_released: ilck_state.triggerentry == 0'),
      L('src/app/driver/interlock/interlock.c', 'void ILCK_Trigger(void) {', 'proven', 'no_illegal_request_counted: ilck_state.ErrRequestCounter == 0'),
      L('src/app/driver/interlock/interlock.c', 'void ILCK_Trigger(void) {', 'proven', 'timer_bounded: ilck_state.timer <= ILCK_STATEMACH_SHORTTIME'),
    ],
  },
]
