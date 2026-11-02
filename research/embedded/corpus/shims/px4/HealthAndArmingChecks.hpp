// PX4's health and arming checks (other code): what the arming state machine asks of them. The checks themselves
// (sensors, estimator, battery, ...) are another module's; their verdict is the request's.
#pragma once
#include <stdint.h>
#include <px4_platform_common/events.h>
#include <uORB/topics/vehicle_status.h>
#include <systemlib/mavlink_log.h>
#include <drivers/drv_hrt.h>
class HealthAndArmingChecks {
public:
	bool update(bool force_reporting = false);
	bool canArm(uint8_t nav_state) const;
};
