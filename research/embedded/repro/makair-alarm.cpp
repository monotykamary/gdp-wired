// MakAir's Alarm (srcs/alarm.cpp at 042ad55), compiled as it ships: the runs the CLI gives for first_detection_counts
// (broken) and cycles_counted_only_when_triggered (unknown, false 256 detections deep).
#include "srcs/alarm.cpp"
#include <cstdio>
int main() {
  Alarm a(ALARM_HIGH, 11u, 1u);
  a.detected(4294967295u);
  std::printf("first_detection_counts: threshold 1, detected(4294967295) right after construction: triggered=%d (the law says 1)\n", a.isTriggered());
  Alarm b(ALARM_HIGH, 11u, 255u);
  for (uint32_t c = 0; c < 255; c++) b.detected(c);
  std::printf("threshold 255, 255 detections: triggered=%d\n", b.isTriggered());
  b.detected(255u);
  std::printf("cycles_counted_only_when_triggered: the 256th detection: triggered=%d, cycles since trigger=%u (the count wrapped to 0)\n", b.isTriggered(), b.getCyclesSinceTrigger());
  return 0;
}
