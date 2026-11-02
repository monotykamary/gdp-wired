// PX4's events interface (other code), as the arming state machine calls it, and the generated enums it names.
#pragma once
#include <stdint.h>
namespace events {
enum class Log : uint8_t { Emergency, Alert, Critical, Error, Warning, Notice, Info, Debug };
constexpr uint32_t ID(const char *) { return 0; }
template <typename... T, typename... A> void send(uint32_t id, Log level, const char *message, A... args);
namespace px4 { namespace enums {
enum class arming_state_t : uint8_t { init = 0, standby = 1, armed = 2, standby_error = 3, shutdown = 4, inair_restore = 5 };
enum class arm_disarm_reason_t : uint8_t { transition_to_standby = 0, rc_stick = 1, rc_switch = 2, command_internal = 3, command_external = 4 };
} }
}
// (PX4's arming state: a vehicle_status_s ARMING_STATE_* value)
typedef uint8_t arming_state_t;
