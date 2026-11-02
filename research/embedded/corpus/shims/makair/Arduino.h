// The Arduino core's interface as the firmware uses it (the STM32 core's declarations; bodies are the board's).
#pragma once
#include <stdint.h>
#include <stdbool.h>
#define HIGH 0x1
#define LOW 0x0
#define PD2 2
#ifdef __cplusplus
extern "C" {
#endif
uint32_t millis(void);
uint32_t micros(void);
void digitalWrite(uint32_t pin, uint32_t value);
int digitalRead(uint32_t pin);
void delay(uint32_t ms);
#ifdef __cplusplus
}
#endif
