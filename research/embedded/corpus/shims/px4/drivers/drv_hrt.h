// PX4's high-resolution timer (other code): the time since boot, in microseconds.
#pragma once
#include <stdint.h>
typedef uint64_t hrt_abstime;
extern "C" hrt_abstime hrt_absolute_time(void);
