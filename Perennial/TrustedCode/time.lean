/-
Trusted model of `time` (namespace `time`, as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace time
section code
variable [FfiSyntax] [GoGlobalContext]

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

end Perennial
