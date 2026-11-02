// PX4's MAVLink log (other code): the critical message the arming state machine sends.
#pragma once
typedef void *orb_advert_t;
extern "C" void mavlink_log_emit(orb_advert_t *pub, const char *fmt, ...);
#define mavlink_log_critical(_pub, _text, ...) mavlink_log_emit(_pub, _text, ##__VA_ARGS__)
