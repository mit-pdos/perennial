#include "textflag.h"

// func GetTSC() uint64
TEXT ·GetTSC(SB),NOSPLIT,$0-8
	MRS  CNTVCT_EL0, R0
	MOVD R0, ret+0(FP)
	RET
