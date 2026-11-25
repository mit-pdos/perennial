// The Go model of the runtime's clock readings of package time
// (Perennial/Code/time.toml, [model]), spliced into time.go in place of the
// bodyless declarations the runtime defines by linkname. They read the clock
// through now (time.go, also defined by the runtime), a primitive stub
// (TrustedCode/time.lean: arbitrary readings), which gc links to the runtime's
// real clock as before.

package time

import "internal/gomodel"

// MODEL: the runtime's runtimeNow (runtime/time.go, time_runtimeNow) is
//
//	if bubble := getg().bubble; bubble != nil {
//		return bubble.now / 1e9, int32(bubble.now % 1e9), 0
//	}
//	return time_now()
//
// and time_now is time.now's definition. The model returns now(), whose model
// is any (sec, nsec, mono); so it covers the bubble's fake clock too.
func runtimeNow() (sec int64, nsec int32, mono int64) {
	return now()
}

// MODEL: the runtime's runtimeNano (time_runtimeNano) is the bubble's fake
// clock inside a testing/synctest bubble, else nanotime(), the monotonic
// clock that now() also returns as mono. Both are positive: on Linux nanotime
// is CLOCK_MONOTONIC, the time since boot, and a bubble's clock starts at
// 2000-01-01 UTC; `when` relies on it ("runtimeNano() and d are always
// positive"), and the runtime's timers throw on a non-positive when. The model
// returns now()'s mono, with a non-positive one (which no Go run reads)
// replaced by 1, so that its readings are positive as Go's are and the
// models' timers can keep the runtime's throws (startTimer).
func runtimeNano() int64 {
	_, _, mono := now()
	if mono <= 0 {
		mono = 1
	}
	return mono
}

// MODEL: the runtime's runtimeIsBubbled is true exactly inside a
// testing/synctest bubble; the model has both results (gomodel.Choose).
func runtimeIsBubbled() bool {
	return gomodel.Choose()
}
