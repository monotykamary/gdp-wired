/* A stand-in for the TI HALCoGen N2HET register block as the interlock configuration names it (the board's generated header). */
#pragma once
#include <stdint.h>
typedef volatile struct hetBase { uint32_t DIR; uint32_t DIN; uint32_t DOUT; uint32_t DSET; uint32_t DCLR; } hetBASE_t;
#define hetREG1 ((hetBASE_t *)0xFFF7B800U)
