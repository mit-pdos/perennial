package grove_ffi

import (
	"time"
)

func GetTimeRange() (uint64, uint64) {
	// XXX: get true error bounds using ntp
	t := uint64(time.Now().UnixNano())
	return t, t + 10e6
}
