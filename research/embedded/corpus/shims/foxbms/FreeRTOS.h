/* A stand-in for FreeRTOS's handle types as foxBMS's os.h names them (the kernel is other code). */
#pragma once
#include <stdint.h>
typedef void *TaskHandle_t; typedef void *QueueHandle_t; typedef void *SemaphoreHandle_t; typedef uint32_t TickType_t; typedef long BaseType_t; typedef unsigned long UBaseType_t;
#define configMINIMAL_STACK_SIZE 128
#define portTICK_RATE_MS 1
#define configUSE_TIMERS 0
#define configSUPPORT_STATIC_ALLOCATION 0
typedef struct { int x; } StaticTask_t; typedef uint32_t StackType_t; typedef struct { int x; } StaticQueue_t;
