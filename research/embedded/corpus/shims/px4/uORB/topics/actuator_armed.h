// The uORB topic actuator_armed (msg/ActuatorArmed.msg, PX4 v1.14.3), as generated.
#pragma once
#include <stdint.h>
struct actuator_armed_s {
	uint64_t timestamp;
	bool armed;
	bool prearmed;
	bool ready_to_arm;
	bool lockdown;
	bool manual_lockdown;
	bool force_failsafe;
	bool in_esc_calibration_mode;
};
