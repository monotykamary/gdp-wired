// CANopenNode's node guarding slave (301/CO_Node_Guarding.c at 9b8beed), compiled as it ships with the example port:
// the run the CLI gives for disable_clears_the_timeout (broken).
#include "301/CO_Node_Guarding.c"
#include <stdio.h>
CO_ReturnError_t CO_CANsend(CO_CANmodule_t *m, CO_CANtx_t *b) { (void)m; (void)b; return CO_ERROR_NO; }
void CO_error(CO_EM_t *em, bool_t setError, const uint8_t errorBit, uint16_t errorCode, uint32_t infoCode) { (void)em; printf("  CO_error(%s, bit %u, code 0x%04x)\n", setError ? "set" : "reset", errorBit, errorCode); (void)infoCode; }
// (the object dictionary's readers, whose addresses the file's init takes: never called here)
ODR_t OD_readOriginal(OD_stream_t *s, void *b, OD_size_t c, OD_size_t *r) { (void)s; (void)b; (void)c; (void)r; return ODR_OK; }
ODR_t OD_writeOriginal(OD_stream_t *s, const void *b, OD_size_t c, OD_size_t *w) { (void)s; (void)b; (void)c; (void)w; return ODR_OK; }
int main(void) {
  static CO_nodeGuardingSlave_t ngs; static CO_CANtx_t buf;
  ngs.CANtxBuff = &buf; ngs.lifeTime_us = 1000;
  CO_FLAG_SET(ngs.CANrxNew);
  CO_nodeGuardingSlave_process(&ngs, CO_NMT_OPERATIONAL, false, 10, NULL);
  printf("a guard request: lifeTimer=%u timeout=%d\n", ngs.lifeTimer, ngs.lifeTimeTimeout);
  CO_nodeGuardingSlave_process(&ngs, CO_NMT_OPERATIONAL, false, 1000, NULL);
  printf("1000 us without one: lifeTimer=%u timeout=%d\n", ngs.lifeTimer, ngs.lifeTimeTimeout);
  CO_nodeGuardingSlave_process(&ngs, CO_NMT_OPERATIONAL, true, 10, NULL);
  printf("disable_clears_the_timeout: the slave disabled: lifeTimer=%u timeout=%d (the law says 0)\n", ngs.lifeTimer, ngs.lifeTimeTimeout);
  return 0;
}
