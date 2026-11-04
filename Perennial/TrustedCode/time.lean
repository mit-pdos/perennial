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

/-- The address of the runtime's state of the timer whose `Timer` (or `Ticker`) is at `t`. The
runtime allocates a timer as a `runtime.timeTimer`, the `Timer`'s fields followed by the
embedded `timer`; this is that `timer`, as one cell. -/
def runtimeTimerRef : val :=
  λ: "t", StructFieldRef (go.Named go!"time.Timer" []) go!"timer" "t"

/-- Allocates the runtime's state of the timer at `t`. -/
def runtimeTimerAlloc : val :=
  λ: "t",
    let: "r" := GoAlloc go.bool #true in
    if: "r" =⟨go.PointerType go.bool⟩ runtimeTimerRef "t" then #() else AngelicExit #()

/-- The runtime's `stopTimer(t)` (a `go:linkname`): some `bool`, for one of the runtime's
timers. The runtime also stops the timer; the model's timers have no state to stop. -/
def stopTimer.impl : val :=
  λ: "t",
    ![go.bool] (runtimeTimerRef "t") ;;
    ArbitraryInt =⟨go.int64⟩ #(W64 0)

/-- The runtime's `resetTimer(t, when, period)` (a `go:linkname`): some `bool`, for one of the
runtime's timers. The runtime also reschedules the timer; the model's timers have no schedule. -/
def resetTimer.impl : val :=
  λ: "t" "when" "period",
    ![go.bool] (runtimeTimerRef "t") ;;
    ArbitraryInt =⟨go.int64⟩ #(W64 0)

/-- The runtime's `newTimer(when, period, f, arg, cp)` (a `go:linkname`): a new `*Timer` with
`initTimer` set (and no channel; `NewTimer` sets `C` itself), whose runtime timer calls
`f(arg, seq, delta)` from a goroutine when it fires, once, or every `period` if `period ≠ 0`.
Modeled as a goroutine that calls `f` (with arbitrary `seq` and `delta`) once, or repeatedly if
`period ≠ 0`. The delay is a no-op, and an execution in which the timer never fires (it is
stopped first, or `when` is never reached) is a prefix of the model's executions. Not modeled:
`Reset` (the runtime may then call `f` again). -/
def newTimer.impl : val :=
  λ: "when" "period" "f" "arg" "cp",
    let: "t" := GoAlloc (go.Named go!"time.Timer" [])
      (CompositeLiteral (go.Named go!"time.Timer" []) (LiteralValue [
        KeyedElement (some (KeyField go!"initTimer")) (ElementExpression go.bool #true)
      ])) in
    runtimeTimerAlloc "t" ;;
    Fork ((rec: "fire" <> :=
        "f" "arg" ArbitraryInt ArbitraryInt ;;
        if: "period" =⟨go.int64⟩ #(W64 0) then #() else "fire" #()) #()) ;;
    "t"

def runtimeNano.impl : val :=
  λ: <>, ArbitraryInt

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

def After.impl : val :=
  λ: "d",
    let: "ch" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() #(W64 0) in
    -- delay is modeled as a no-op
    Fork (chan.send (go.Named go!"time.Time" []) "ch" (arbitraryTime #())) ;;
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
state (`runtimeTimerAlloc`). Each firing of Go's timer calls `sendTime`, a non-blocking send of
the current time on `c`; the model forks a goroutine that sends arbitrary times on `c` forever,
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
    runtimeTimerAlloc "t" ;;
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
    runtimeTimerAlloc "t" ;;
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
reader could not load the variable (nothing gives a points-to for it). -/
def asynctimerchan.init : val :=
  λ: <>, #()

end code
end time

end

end Perennial
