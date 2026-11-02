// The uORB topic vehicle_status as PX4 v1.14.3 generates it from msg/VehicleStatus.msg: the fields and constants the
// arming state machine reads (a stand-in for the generated header).
#pragma once
#include <stdint.h>
struct vehicle_status_s {
	uint64_t timestamp;
	uint64_t armed_time;
	uint64_t takeoff_time;
	uint8_t arming_state;
	uint8_t latest_arming_reason;
	uint8_t latest_disarming_reason;
	uint8_t nav_state;
	uint8_t hil_state;
	static constexpr uint8_t ARMING_STATE_INIT = 0;
	static constexpr uint8_t ARMING_STATE_STANDBY = 1;
	static constexpr uint8_t ARMING_STATE_ARMED = 2;
	static constexpr uint8_t ARMING_STATE_STANDBY_ERROR = 3;
	static constexpr uint8_t ARMING_STATE_SHUTDOWN = 4;
	static constexpr uint8_t ARMING_STATE_IN_AIR_RESTORE = 5;
	static constexpr uint8_t ARMING_STATE_MAX = 6;
	static constexpr uint8_t HIL_STATE_OFF = 0;
	static constexpr uint8_t HIL_STATE_ON = 1;
};
