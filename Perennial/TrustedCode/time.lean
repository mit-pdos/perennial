/-
Trusted model of `time` (namespace `time`, as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial
noncomputable section

namespace time
section code
variable [GooseExts] [GoGlobalContext]

/-- The type of the runtime's state of a timer in the model: what the timer does when it fires. -/
def runtimeTimerType : go.GoType := go.GoType.FunctionType (go.signature.Signature [] false [])

/-- The address of the runtime's state of the timer whose `Timer` (or `Ticker`) is at `t`. The
runtime allocates a timer as a `runtime.timeTimer`, the `Timer`'s fields followed by the
embedded `timer`; this is that `timer`, as one cell, which holds what the timer does when it
fires. -/
def runtimeTimerRef : val :=
  λ: "t", StructFieldRef (go.Named go!"time.Timer" []) go!"timer" "t"

/-- Allocates the runtime's state of the timer at `t`, which fires by calling `fire`. -/
def runtimeTimerAlloc : val :=
  λ: "t" "fire",
    let: "r" := GoAlloc runtimeTimerType "fire" in
    if: "r" =⟨go.PointerType runtimeTimerType⟩ runtimeTimerRef "t" then #() else AngelicExit #()

/-- The runtime's `stopTimer(t)` (a `go:linkname`): some `bool`, for one of the runtime's
timers. The runtime also stops the timer; the model's timers may fire regardless. -/
def stopTimer.impl : val :=
  λ: "t",
    ![runtimeTimerType] (runtimeTimerRef "t") ;;
    ArbitraryInt =⟨go.int64⟩ #(W64 0)

/-- The runtime's `resetTimer(t, when, period)` (a `go:linkname`): some `bool`, for one of the
runtime's timers, which fires (again): the model forks one more firing. The delay is a no-op,
and the timer's earlier firings may still happen. -/
def resetTimer.impl : val :=
  λ: "t" "when" "period",
    let: "fire" := ![runtimeTimerType] (runtimeTimerRef "t") in
    Fork ("fire" #()) ;;
    ArbitraryInt =⟨go.int64⟩ #(W64 0)

/-- The runtime's `newTimer(when, period, f, arg, cp)` (a `go:linkname`): a new `*Timer` with
`initTimer` set (and no channel; `NewTimer` sets `C` itself), whose runtime timer calls
`f(arg, seq, delta)` from a goroutine when it fires, once, or every `period` if `period ≠ 0`.
Modeled as a goroutine that calls `f` (with arbitrary `seq` and `delta`) once, or repeatedly if
`period ≠ 0`; the runtime's state holds that call, which `resetTimer` forks again. The delay is
a no-op, and an execution in which the timer never fires (it is stopped first, or `when` is
never reached) is a prefix of the model's executions. -/
def newTimer.impl : val :=
  λ: "when" "period" "f" "arg" "cp",
    let: "t" := GoAlloc (go.Named go!"time.Timer" [])
      (CompositeLiteral (go.Named go!"time.Timer" []) (LiteralValue [
        KeyedElement (some (KeyField go!"initTimer")) (ElementExpression go.bool #true)
      ])) in
    let: "fire" := (λ: <>, "f" "arg" ArbitraryInt ArbitraryInt) in
    runtimeTimerAlloc "t" "fire" ;;
    Fork ((rec: "loop" <> :=
        "fire" #() ;;
        if: "period" =⟨go.int64⟩ #(W64 0) then #() else "loop" #()) #()) ;;
    "t"

def runtimeNano.impl : val :=
  λ: <>, ArbitraryInt

/-- `runtimeNow` (a `go:linkname` into the runtime) reads the wall clock, as seconds and
nanoseconds since the Unix epoch, and the monotonic clock; modeled as arbitrary values of its
result types `(int64, int32, int64)`, which include every result of the runtime (there `nsec` is
below 1e9, and `mono` is 0 on a platform without a monotonic clock). -/
def runtimeNow.impl : val :=
  λ: <>, Pair (Pair ArbitraryInt (Convert go.int64 go.int32 ArbitraryInt)) ArbitraryInt

/-- `runtimeIsBubbled` (a `go:linkname` into the runtime) is true only inside a
`testing/synctest` bubble; modeled as an arbitrary boolean. -/
def runtimeIsBubbled.impl : val :=
  λ: <>, ArbitraryInt =⟨go.int64⟩ #(W64 0)

-- TODO: could avoid making this trusted by verifying the real implementation,
-- which requires verifying `internal/godebug`.
def syncTimer.impl : val :=
  λ: "c",
     if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then "c"
     else #chan.nil

def arbitraryTime : val :=
  λ: <>,
     -- generate a simple non-monotonic time without any nanoseconds and
     -- location of UTC
     let: "wall_seconds" := ArbitraryInt in
     CompositeLiteral (go.Named go!"time.Time" []) (LiteralValue [
        KeyedElement (some (KeyField go!"wall")) (ElementExpression go.uint64 #(W64 0)),
        KeyedElement (some (KeyField go!"ext")) (ElementExpression go.int64 "wall_seconds"),
        KeyedElement (some (KeyField go!"loc")) (ElementExpression «unsafe».Pointer #null)
     ])

/-! ### The runtime's monotonic clock

Go's runtime reads the machine's monotonic clock (`runtime.nanotime`, `CLOCK_MONOTONIC` on Linux:
nanoseconds, an `int64`), which never goes back: every reading is at least every reading before it,
in every goroutine. The model keeps it as runtime state, as it keeps the runtime's timers
(`runtimeTimerRef`): a cell holding the clock's current value, reached from the model-only global
`time.runtimeClock` (no Go variable has that name, so no Go program reads or writes it). A reading
(`runtimeClockNow`) advances the clock by an arbitrary amount (zero included) and returns the new
value; so the readings of a run are exactly the non-decreasing sequences of `int64`s, which include
every sequence the real clock produces.

A program observes the clock only through the timers that wait for it (the readings are not
returned to Go code: `After` sends an arbitrary time), so the model removes no execution of Go's:
any order of `After` calls and firings is one of the model's, with the clock advanced at each firing
as far as it needs. What the model adds is a clock that the proofs can speak of (`time.clockLb`), and
its claim that the machine's monotonic clock is one of its evolutions: Go's timers fire only once
`nanotime() >= when`, and `nanotime` never goes back. (A `testing/synctest` bubble, whose timers
follow a fake clock, is outside the model: `internal/synctest`'s `Run` is a stuck `Panic`.)

Only `After` reads this clock so far; `runtimeNano`, `runtimeNow` and the other timers keep their
arbitrary readings (a superset of the real ones, so still sound), so that their specs need not take
the package's `isPkgInit`. -/

/-- The name of the model-only global holding the address of the clock's cell. -/
def runtimeClock : GoString := go!"time.runtimeClock"

/-- The global's type: a pointer (the clock's cell is an untyped cell holding an `int64`, which no Go
type describes; only this file reads or writes it). -/
def runtimeClockType : go.GoType := go.GoType.PointerType go.int64

/-- Allocates the runtime clock (called by the initializer of `asynctimerchan`, below): the global
`time.runtimeClock`, holding the address of a fresh cell holding an arbitrary `int64`, the clock's
reading when the program starts. -/
def runtimeClockInit : val :=
  λ: <>,
    go.GlobalAlloc runtimeClock runtimeClockType #() ;;
    GlobalVarAddr runtimeClock #() <-[runtimeClockType] (Alloc ArbitraryInt)

/-- A reading of the runtime clock whose cell is at `l`: advances the clock to an arbitrary value
`n` at least its current one `c` and returns `n`. Linearizable at the `CAS`, which fails, and the
reading starts over, if another reading advanced the clock in between (the loop may spin forever,
which the real clock does not: the model covers partial correctness only). `c` is read with an
atomic add of 0. -/
def runtimeClockRead : val :=
  rec: "loop" "l" :=
    let: "c" := AtomicAdd "l" #(W64 0) in
    let: "n" := ArbitraryInt in
    if: "c" ≤⟨go.int64⟩ "n" then
      (if: CAS "l" "c" "n" then "n" else "loop" "l")
    else "loop" "l"

/-- A reading of the runtime clock (`runtimeClockRead` of its cell). -/
def runtimeClockNow : val :=
  λ: <>, runtimeClockRead (![runtimeClockType] (GlobalVarAddr runtimeClock #()))

/-- Waits until the runtime clock reaches `w`, and returns that reading (at least `w`). The model
spins on readings, where the runtime parks the goroutine until the clock reaches `w`: the same
outcomes, under partial correctness (a run in which the clock never gets there spins forever). -/
def runtimeClockWaitUntil : val :=
  rec: "loop" "w" :=
    let: "x" := runtimeClockNow #() in
    if: "w" ≤⟨go.int64⟩ "x" then "x" else "loop" "w"

/-- `After(d)` (`time/sleep.go`) is `NewTimer(d).C`:

```go
func NewTimer(d Duration) *Timer {
	c := make(chan Time, 1)
	t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
	t.C = c
	return t
}

func when(d Duration) int64 {
	if d <= 0 {
		return runtimeNano()
	}
	t := runtimeNano() + int64(d)
	if t < 0 {
		// N.B. runtimeNano() and d are always positive, so addition
		// (including overflow) will never result in t == 0.
		t = 1<<63 - 1 // math.MaxInt64
	}
	return t
}
```

The channel has capacity 0 or 1 (see `NewTimer`). The model computes `when(d)` as Go does, over a
reading of the runtime clock (`runtimeClockNow`) in place of `runtimeNano()` (the same clock), and
forks a goroutine that waits until the clock reaches it (the runtime fires the timer once
`nanotime() >= when`) and then sends one arbitrary time on the channel (Go sends the current time,
one of them). The timer is not reachable from the program, so it is never stopped or reset. -/
def After.impl : val :=
  λ: "d",
    let: "ch" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() (if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then #(W64 0) else #(W64 1)) in
    let: "now" := runtimeClockNow #() in
    let: "when" := (if: "d" ≤⟨go.int64⟩ #(W64 0) then "now" else
      let: "t" := "now" +⟨go.int64⟩ "d" in
      if: "t" <⟨go.int64⟩ #(W64 0) then #(W64 (2 ^ 63 - 1)) else "t") in
    Fork (runtimeClockWaitUntil "when" ;;
      chan.send (go.Named go!"time.Time" []) "ch" (arbitraryTime #())) ;;
    "ch"

def Sleep.impl : val :=
  λ: "d", #()

/-- `NewTimer(d)` (`time/sleep.go`):

```go
func NewTimer(d Duration) *Timer {
	c := make(chan Time, 1)
	t := newTimer(when(d), 0, sendTime, c, syncTimer(c))
	t.C = c
	return t
}
```

When `syncTimer(c) != nil` (GODEBUG `asynctimerchan=0`, the default), the runtime's `newTimer`
makes `c` synchronous: its `cap` and `len` are 0. The model makes `c` with capacity 0 or 1,
chosen arbitrarily, and returns a fresh `*Timer` with `C = c`, `initTimer` set and the runtime's
state (`runtimeTimerAlloc`), whose firing does nothing of its own. Each firing of Go's timer
calls `sendTime`, a non-blocking send of the current time on `c`; the model forks a goroutine that
sends arbitrary times on `c` forever, covering every firing, including those after a `Reset`,
which allows more (values after `Stop` or `Reset`, stale values), and an execution in which
the timer never fires is a prefix of the model's. -/
def NewTimer.impl : val :=
  λ: "d",
    let: "c" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() (if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then #(W64 0) else #(W64 1)) in
    let: "t" := GoAlloc (go.Named go!"time.Timer" [])
      (CompositeLiteral (go.Named go!"time.Timer" []) (LiteralValue [
        KeyedElement (some (KeyField go!"C"))
          (ElementExpression (go.ChannelType go.recvonly (go.Named go!"time.Time" [])) "c"),
        KeyedElement (some (KeyField go!"initTimer")) (ElementExpression go.bool #true)
      ])) in
    runtimeTimerAlloc "t" (λ: <>, #()) ;;
    Fork ((rec: "tick" <> :=
        chan.send (go.Named go!"time.Time" []) "c" (arbitraryTime #()) ;; "tick" #()) #()) ;;
    "t"

/-- `NewTicker(d)` (`time/tick.go`):

```go
func NewTicker(d Duration) *Ticker {
	if d <= 0 {
		panic("non-positive interval for NewTicker")
	}
	c := make(chan Time, 1)
	t := (*Ticker)(unsafe.Pointer(newTimer(when(d), int64(d), sendTime, c, syncTimer(c))))
	t.C = c
	return t
}
```

Go reinterprets the runtime's new `*Timer` as a `*Ticker` (`Ticker` is `Timer`'s prefix: `C` and
`initTicker`, at `Timer`'s `C` and `initTimer`), which goose cannot translate. The model keeps
the panic and is `NewTimer`'s otherwise: a channel of capacity 0 or 1, a fresh `*Ticker` with
`C = c`, `initTicker` set and the runtime's state, and a goroutine that sends arbitrary times on
`c` forever (the runtime's periodic `sendTime`; the delay between ticks is a no-op). -/
def NewTicker.impl : val :=
  λ: "d",
    if: "d" ≤⟨go.int64⟩ #(W64 0) then Panic "non-positive interval for NewTicker" else
    let: "c" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() (if: ArbitraryInt =⟨go.int64⟩ #(W64 0) then #(W64 0) else #(W64 1)) in
    let: "t" := GoAlloc (go.Named go!"time.Ticker" [])
      (CompositeLiteral (go.Named go!"time.Ticker" []) (LiteralValue [
        KeyedElement (some (KeyField go!"C"))
          (ElementExpression (go.ChannelType go.recvonly (go.Named go!"time.Time" [])) "c"),
        KeyedElement (some (KeyField go!"initTicker")) (ElementExpression go.bool #true)
      ])) in
    runtimeTimerAlloc "t" (λ: <>, #()) ;;
    Fork ((rec: "tick" <> :=
        chan.send (go.Named go!"time.Time" []) "c" (arbitraryTime #()) ;; "tick" #()) #()) ;;
    "t"

/-- `(*Ticker).Stop()` (`time/tick.go`):

```go
func (t *Ticker) Stop() {
	if !t.initTicker {
		return
	}
	stopTimer((*Timer)(unsafe.Pointer(t)))
}
```

The conversion is the identity on the address (goose cannot translate it: `Timer` is not
plain). -/
def Ticker.Stop.impl : val :=
  λ: "t" <>,
    if: ![go.bool] (StructFieldRef (go.Named go!"time.Ticker" []) go!"initTicker" "t")
    then stopTimer.impl "t" ;; #() else #()

/-- `(*Ticker).Reset(d)` (`time/tick.go`):

```go
func (t *Ticker) Reset(d Duration) {
	if d <= 0 {
		panic("non-positive interval for Ticker.Reset")
	}
	if !t.initTicker {
		panic("time: Reset called on uninitialized Ticker")
	}
	resetTimer((*Timer)(unsafe.Pointer(t)), when(d), int64(d))
}
```

As `Stop`; `when(d)` is not computed (it cannot panic, and the model's `resetTimer` ignores it). -/
def Ticker.Reset.impl : val :=
  λ: "t" "d",
    if: "d" ≤⟨go.int64⟩ #(W64 0) then Panic "non-positive interval for Ticker.Reset" else
    if: ![go.bool] (StructFieldRef (go.Named go!"time.Ticker" []) go!"initTicker" "t")
    then resetTimer.impl "t" #(W64 0) "d" ;; #()
    else Panic "time: Reset called on uninitialized Ticker"

/-- The initializer of `asynctimerchan` (`time/sleep.go`):

```go
var asynctimerchan = godebug.New("asynctimerchan")
```

The model does nothing, and `asynctimerchan` is not allocated. `internal/godebug` is not
translated; its `New(name)` is `return &Setting{name: name}`, an allocation, so Go's
initializer cannot panic and has no effect beyond the variable. Its only reader is
`syncTimer` (`asynctimerchan.Value()`, which reads the `GODEBUG` setting the runtime hands to
`internal/godebug`), whose model above chooses either result arbitrarily instead; a translated
reader could not load the variable (nothing gives a points-to for it).

The model also allocates the runtime clock (`runtimeClockInit`), which Go's runtime has from the
program's start: it is the only trusted code of `time`'s initialization, which runs before any
reading of the clock (only `After` reads it, which no initializer of `time` calls), and no other
package's initialization can call into `time` before it. -/
def asynctimerchan.init : val :=
  λ: <>, runtimeClockInit #()

end code
end time

end

end Perennial
