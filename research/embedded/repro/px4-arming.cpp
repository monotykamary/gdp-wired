// PX4's ArmStateMachine (v1.14.3), compiled as it ships against the corpus's stand-ins for its environment: the runs the
// CLI gives for shutdown_is_final and denied_changes_nothing (both broken, in HIL).
#include "src/modules/commander/Arming/ArmStateMachine/ArmStateMachine.cpp"
#include <cstdio>
bool HealthAndArmingChecks::update(bool) { return true; }
bool HealthAndArmingChecks::canArm(uint8_t) const { return true; }
extern "C" void mavlink_log_emit(orb_advert_t *, const char *, ...) {}
extern "C" hrt_abstime hrt_absolute_time(void) { return 1; }
namespace events { template <typename... T, typename... A> void send(uint32_t, Log, const char *, A...) {} }
int main() {
  vehicle_status_s status{}; actuator_armed_s armed{}; HealthAndArmingChecks checks; orb_advert_t pub = nullptr;
  status.hil_state = vehicle_status_s::HIL_STATE_ON;
  ArmStateMachine m;
  m.forceArmState(vehicle_status_s::ARMING_STATE_SHUTDOWN);
  transition_result_t r = m.arming_state_transition(status, vehicle_status_s::ARMING_STATE_STANDBY, armed, checks, true, &pub, arm_disarm_reason_t::command_internal);
  std::printf("shutdown_is_final: HIL on, from SHUTDOWN, request STANDBY: result=%d state=%u (SHUTDOWN is %u)\n", (int)r, m.getArmState(), vehicle_status_s::ARMING_STATE_SHUTDOWN);
  ArmStateMachine n;
  n.forceArmState(vehicle_status_s::ARMING_STATE_STANDBY_ERROR);
  r = n.arming_state_transition(status, vehicle_status_s::ARMING_STATE_ARMED, armed, checks, true, &pub, arm_disarm_reason_t::command_internal);
  std::printf("denied_changes_nothing: HIL on, from STANDBY_ERROR (%u), request ARMED: result=%d (DENIED is %d) state=%u\n", vehicle_status_s::ARMING_STATE_STANDBY_ERROR, (int)r, (int)TRANSITION_DENIED, n.getArmState());
  return 0;
}
