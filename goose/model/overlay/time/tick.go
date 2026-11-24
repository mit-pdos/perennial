// The Go model of package time's tickers (Perennial/Code/time.toml, [model]),
// spliced into tick.go in place of the real declarations: NewTicker and
// Ticker's Stop and Reset, whose Go converts between *Timer and *Ticker
// through unsafe.Pointer (the semantics converts an unsafe.Pointer only to a
// pointer to a plain type, Golang/Defn/Plain.lean). The timers are
// sleep.go's models.

package time

import "unsafe"

// MODEL: Go's NewTicker is
//
//	if d <= 0 {
//		panic("non-positive interval for NewTicker")
//	}
//	c := make(chan Time, 1)
//	t := (*Ticker)(unsafe.Pointer(newTimer(when(d), int64(d), sendTime, c, syncTimer(c))))
//	t.C = c
//	return t
//
// The model keeps the panic and is NewTimer's model otherwise (the channel,
// sendTimes), with the runtime's timer allocated as a Ticker
// (newRuntimeTicker) in place of the conversion, and armed with period d.
func NewTicker(d Duration) *Ticker {
	if d <= 0 {
		panic("non-positive interval for NewTicker")
	}
	c := makeTimerChan()
	w := when(d)
	fire := timerFunc(sendTimes, c)
	checkWhen(w, int64(d))
	t := newRuntimeTicker(fire)
	startTimer(fire, w, int64(d))
	t.C = c
	return t
}

// MODEL: Go's Stop is
//
//	if !t.initTicker {
//		return
//	}
//	stopTimer((*Timer)(unsafe.Pointer(t)))
//
// The model is the same with stopTimer's model at t's address (stopTimerAt)
// in place of the conversion, which is the identity on the address.
func (t *Ticker) Stop() {
	if !t.initTicker {
		return
	}
	stopTimerAt(unsafe.Pointer(t))
}

// MODEL: Go's Reset is
//
//	if d <= 0 {
//		panic("non-positive interval for Ticker.Reset")
//	}
//	if !t.initTicker {
//		panic("time: Reset called on uninitialized Ticker")
//	}
//	resetTimer((*Timer)(unsafe.Pointer(t)), when(d), int64(d))
//
// The model is the same with resetTimer's model at t's address
// (resetTimerAt) in place of the conversion.
func (t *Ticker) Reset(d Duration) {
	if d <= 0 {
		panic("non-positive interval for Ticker.Reset")
	}
	if !t.initTicker {
		panic("time: Reset called on uninitialized Ticker")
	}
	resetTimerAt(unsafe.Pointer(t), when(d), int64(d))
}
