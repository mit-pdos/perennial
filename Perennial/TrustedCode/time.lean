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

/-- The runtime's `newTimer(when, period, f, arg, cp)` (a `go:linkname`): a new `*Timer` with
`initTimer` set (and no channel; `NewTimer` sets `C` itself), whose runtime timer calls
`f(arg, seq, delta)` from a goroutine when it fires, once, or every `period` if `period ≠ 0`.
Modeled as a goroutine that calls `f` (with arbitrary `seq` and `delta`) once, or repeatedly if
`period ≠ 0`. The delay is a no-op, and an execution in which the timer never fires (it is
stopped first, or `when` is never reached) is a prefix of the model's executions. Not modeled:
`Reset` (the runtime may then call `f` again); `Timer.Reset` is an axiom about `NewTimer`'s
timers only. -/
def newTimer.impl : val :=
  λ: "when" "period" "f" "arg" "cp",
    let: "t" := GoAlloc (go.Named go!"time.Timer" [])
      (CompositeLiteral (go.Named go!"time.Timer" []) (LiteralValue [
        KeyedElement (some (KeyField go!"initTimer")) (ElementExpression go.bool #true)
      ])) in
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
the panic, makes the channel with Go's capacity, and returns a fresh `*Ticker` with `C = c` and
`initTicker` set (as the runtime's `newTimer` sets `initTimer`, read through the shared prefix).
The runtime's periodic timer calls `sendTime`, which sends the current time on `c` unless the
send would block; the model forks a goroutine that sends an arbitrary time on `c` forever
(`arbitraryTime`, as `After`'s model), blocking while the buffer is full. A receiver can
distinguish neither the times (arbitrary in both) nor the dropped ticks (Go's dropped sends and
the model's blocked one both leave one value in the buffer); the delay between ticks is a no-op,
and an execution in which the ticker never fires is a prefix of the model's. -/
def NewTicker.impl : val :=
  λ: "d",
    if: "d" ≤⟨go.int64⟩ #(W64 0) then Panic "non-positive interval for NewTicker" else
    let: "c" := FuncResolve go.make2 [go.ChannelType go.sendrecv (go.Named go!"time.Time" [])]
      #() #(W64 1) in
    let: "t" := GoAlloc (go.Named go!"time.Ticker" [])
      (CompositeLiteral (go.Named go!"time.Ticker" []) (LiteralValue [
        KeyedElement (some (KeyField go!"C"))
          (ElementExpression (go.ChannelType go.recvonly (go.Named go!"time.Time" [])) "c"),
        KeyedElement (some (KeyField go!"initTicker")) (ElementExpression go.bool #true)
      ])) in
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

The model reads `initTicker` (so that a nil `t` is stuck, as Go's load panics) and does not stop
the ticker's goroutine: a stopped ticker's channel may still deliver in the model, which only
adds executions (as `Timer.Stop`'s specs allow of a stopped timer). -/
def Ticker.Stop.impl : val :=
  λ: "t" <>,
    ![go.bool] (StructFieldRef (go.Named go!"time.Ticker" []) go!"initTicker" "t") ;; #()

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

The model keeps both panics; rescheduling is a no-op (the model's ticks have no timing). -/
def Ticker.Reset.impl : val :=
  λ: "t" "d",
    if: "d" ≤⟨go.int64⟩ #(W64 0) then Panic "non-positive interval for Ticker.Reset" else
    if: ![go.bool] (StructFieldRef (go.Named go!"time.Ticker" []) go!"initTicker" "t")
    then #() else Panic "time: Reset called on uninitialized Ticker"

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
