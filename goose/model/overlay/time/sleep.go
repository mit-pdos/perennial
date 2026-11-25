// The Go model of package time's timers (Perennial/Code/time.toml, [model]),
// spliced into sleep.go in place of the real declarations: the runtime's
// bodyless newTimer, stopTimer and resetTimer, and NewTimer and After. The
// rest of sleep.go (Timer.Stop, Timer.Reset, AfterFunc, when, goFunc) is the
// real Go, translated.
//
// A model timer is a goroutine that waits until the runtime clock
// (runtimeNano) reaches the timer's when and then fires it (startTimer). The
// runtime's state of a timer, which Go keeps after the Timer in the runtime's
// allocation (runtime.timeTimer) where no Go type names it, is the primitive
// stubs newRuntimeTimer, newRuntimeTicker and runtimeTimerFire
// (TrustedCode/time.lean), whose gc bodies keep it after the Timer as the
// runtime does. Sleep, a primitive stub too, is a no-op in GooseLang and the
// runtime's sleep in gc, so gc builds with the overlay keep real-time timers.
// In GooseLang every clock reading is arbitrary, so a timer may fire at any
// time after it is started: the model has every schedule of Go's timers.

package time

import (
	"internal/gomodel"
	"sync/atomic"
	"unsafe"
)

// MODEL: the runtime's newTimer (runtime/time.go) allocates a timer
// (runtime.timeTimer: the Timer's fields, then the runtime's state), sets
// initTimer, and arms it: once the runtime clock reaches when it calls
// f(arg, seq, delay) from the timer goroutine, and again every period if
// period != 0. The arming (timer.modify) throws if when <= 0 or period < 0;
// the model is stuck there (startTimer). Its channel argument cp only makes the
// timer's channel synchronous; NewTimer's and NewTicker's models pass nil and
// choose the channel's kind themselves (makeTimerChan), and AfterFunc passes
// nil. The model calls f with arbitrary seq and delay, so it covers the
// runtime's.
func newTimer(when, period int64, f func(any, uintptr, int64), arg any, cp unsafe.Pointer) *Timer {
	fire := timerFunc(f, arg)
	checkWhen(when, period)
	t := newRuntimeTimer(fire)
	startTimer(fire, when, period)
	return t
}

// MODEL: the runtime's stopTimer stops the runtime's timer t and reports
// whether it stopped it before it fired. The model loads t's runtime state
// (stuck if t is not one of the runtime's timers: a Timer the program
// allocated, or a copy, where Go reads memory that is not a timer) and returns
// an arbitrary bool; it does not stop the timer, whose firings may still
// happen (each one is a schedule of Go's in which Stop came later).
func stopTimer(t *Timer) bool {
	return stopTimerAt(unsafe.Pointer(t))
}

// MODEL: the runtime's resetTimer re-arms t (when, period: the arming throws
// as newTimer's does) and reports whether it was armed. The model loads t's
// runtime state as stopTimer does, is stuck where Go throws, starts one more
// firing goroutine with the state's call (startTimer) and returns an arbitrary
// bool. The earlier firings may still happen (as if Reset came later).
func resetTimer(t *Timer, when, period int64) bool {
	return resetTimerAt(unsafe.Pointer(t), when, period)
}

// MODEL: Go's NewTimer is
//
//	c := make(chan Time, 1)
//	t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
//	t.C = c
//	return t
//
// syncTimer(c) is non-nil unless GODEBUG asynctimerchan=1, and then the
// runtime makes c synchronous: cap(c) and len(c) are 0, and a receive after a
// firing gets a value made at the receive. GooseLang cannot change a channel's
// kind after make, so the model makes c either way (makeTimerChan), and fires
// sendTimes in place of sendTime: sendTime's non-blocking send would drop the
// value on an unbuffered c, where the runtime delivers it at the next receive.
// sendTimes sends blocking, so a receive gets the value whenever it comes (or
// a later one: the model also allows values after Stop or Reset, which Go's
// synchronous channels never deliver).
func NewTimer(d Duration) *Timer {
	c := makeTimerChan()
	t := newTimer(when(d), 0, sendTimes, c, nil)
	t.C = c
	return t
}

// MODEL: Go's After(d) is NewTimer(d).C: a timer that is never stopped or
// reset, whose channel delivers one value once the runtime clock reaches
// when(d). The model is NewTimer's (makeTimerChan, a firing that sends
// blocking, sendTimes), over the model's runtime clock (runtimeClock), which
// the proofs can speak of: when(d) is computed (whenAt) from a reading of that
// clock, and the firing goroutine waits until the clock reaches it
// (runtimeClockWaitUntil). The model's claim on the clock: the readings of
// Go's runtime clock form a non-decreasing sequence of positive int64s
// (runtimeNano), and the model's clock has every such sequence; Go's timer
// fires only once the clock has reached when.
func After(d Duration) <-chan Time {
	c := makeTimerChan()
	w := whenAt(runtimeClockNow(), d)
	checkWhen(w, 0)
	go func() {
		runtimeClockWaitUntil(w)
		sendTimes(c, 0, 0)
	}()
	return c
}

// makeTimerChan is a timer's channel: synchronous (GODEBUG asynctimerchan=0,
// Go's default, whose cap and len are 0) or of capacity 1 (asynctimerchan=1).
// gomodel.Choose: the model does not read GODEBUG.
//
// The kind is fixed here, at make. Go's runtime instead re-reads the setting
// on every cap and len of a timer channel (and at each send), so a program
// that changes GODEBUG while running (os.Setenv("GODEBUG",
// "asynctimerchan=1")) sees cap(t.C) of one timer change from 0 to 1, which
// no channel of the model does (docs/KNOWN_LIMITATIONS.md, "time"). This is
// sound only because the model's runtime-provided setenv hook is stuck on the
// key "GODEBUG": no verified program changes the setting mid-run, and with a
// fixed setting every channel the runtime makes has one kind throughout, which
// is one of the two choices here (as TrustedCode/crypto/fips140.lean fixes its
// GODEBUG setting for the whole run).
func makeTimerChan() chan Time {
	if gomodel.Choose() {
		return make(chan Time, 1)
	}
	return make(chan Time)
}

// sendTimes is the model's sendTime: Go's sends Now().Add(Duration(-delta))
// on c without blocking; this one blocks (see NewTimer).
func sendTimes(c any, seq uintptr, delta int64) {
	c.(chan Time) <- Now().Add(Duration(-delta))
}

// timerFunc is a timer's firing: f(arg, seq, delay) with arbitrary seq and
// delay (gomodel.ChooseUint64: the runtime's sequence number and lateness).
func timerFunc(f func(any, uintptr, int64), arg any) func() {
	return func() {
		f(arg, uintptr(gomodel.ChooseUint64()), int64(gomodel.ChooseUint64()))
	}
}

// checkWhen is stuck where the runtime's timer.modify throws ("timer when
// must be positive", "timer period must be non-negative").
func checkWhen(when, period int64) {
	if when <= 0 || period < 0 {
		gomodel.Stuck()
	}
}

// startTimer arms a timer: a goroutine that waits until the runtime clock
// reaches when, fires, and for period != 0 does so again at the next when.
func startTimer(fire func(), when, period int64) {
	go func() {
		w := when
		for {
			sleepUntil(w)
			fire()
			if period == 0 {
				return
			}
			w = nextWhen(w, period)
		}
	}()
}

// nextWhen is a periodic timer's next when: when + period (saturated, as
// `when` saturates), or now if that has passed already (the runtime skips the
// missed periods; a value for each would only queue up on the channel).
func nextWhen(when, period int64) int64 {
	w := when + period
	if w < 0 {
		w = 1<<63 - 1
	}
	if now := runtimeNano(); w < now {
		w = now
	}
	return w
}

// sleepUntil returns once the runtime clock has reached w.
func sleepUntil(w int64) {
	for {
		now := runtimeNano()
		if w <= now {
			return
		}
		Sleep(Duration(w - now))
	}
}

// stopTimerAt is stopTimer at the timer (or ticker) at p.
func stopTimerAt(p unsafe.Pointer) bool {
	_ = runtimeTimerFire(p)
	return gomodel.Choose()
}

// resetTimerAt is resetTimer at the timer (or ticker) at p.
func resetTimerAt(p unsafe.Pointer, when, period int64) bool {
	fire := runtimeTimerFire(p)
	checkWhen(when, period)
	startTimer(fire, when, period)
	return gomodel.Choose()
}

// newRuntimeTimer is a primitive stub (TrustedCode/time.lean): a new *Timer
// with initTimer set, followed by the runtime's state of the timer, which
// holds its firing; GooseLang keeps that state in a cell that no Go
// allocation has (so runtimeTimerFire is stuck at a Timer the program
// allocated). In gc the state follows the Timer in one allocation, as the
// runtime's timeTimer does.
func newRuntimeTimer(fire func()) *Timer {
	type timeTimer struct {
		Timer
		fire func()
	}
	rt := &timeTimer{Timer: Timer{initTimer: true}, fire: fire}
	return &rt.Timer
}

// newRuntimeTicker is newRuntimeTimer for a *Ticker (initTicker set), which
// the runtime allocates as a Timer (Ticker's fields are Timer's).
func newRuntimeTicker(fire func()) *Ticker {
	type timeTicker struct {
		Ticker
		fire func()
	}
	rt := &timeTicker{Ticker: Ticker{initTicker: true}, fire: fire}
	return &rt.Ticker
}

// runtimeTimerFire is a primitive stub (TrustedCode/time.lean): the firing
// held by the runtime's state of the timer at p, made by newRuntimeTimer or
// newRuntimeTicker (GooseLang: stuck at any other p).
func runtimeTimerFire(p unsafe.Pointer) func() {
	type timeTimer struct {
		Timer
		fire func()
	}
	return (*timeTimer)(p).fire
}

// runtimeClock is the model's runtime clock (After): its latest reading,
// which no Go code but runtimeClockNow reads or writes.
var runtimeClock int64

// runtimeClockNow reads the runtime clock and advances runtimeClock to the
// reading, unless another reading got there first (then it reads again), so
// that its results are non-decreasing across goroutines.
func runtimeClockNow() int64 {
	for {
		c := atomic.LoadInt64(&runtimeClock)
		n := runtimeNano()
		if c <= n && atomic.CompareAndSwapInt64(&runtimeClock, c, n) {
			return n
		}
	}
}

// runtimeClockWaitUntil returns a reading of the runtime clock at least w.
func runtimeClockWaitUntil(w int64) int64 {
	for {
		x := runtimeClockNow()
		if w <= x {
			return x
		}
		Sleep(Duration(w - x))
	}
}

// whenAt is when(d) with now for runtimeNano().
func whenAt(now int64, d Duration) int64 {
	if d <= 0 {
		return now
	}
	t := now + int64(d)
	if t < 0 {
		t = 1<<63 - 1
	}
	return t
}
