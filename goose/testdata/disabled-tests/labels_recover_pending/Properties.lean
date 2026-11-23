/-
Scratch, NOT part of the build (it is outside every lake glob, and imports
nothing): the properties Perennial must be able to prove about the examples in
`recovers/` once the semantics for `recover()` in a deferred named function or
method exists. Every `sorry` here is
a target, not a proof.

Conventions are those of the semantics test proofs
(`Perennial/{Spec,Proof}/github_com/mit_pdos/perennial/goose/testdata/examples/semantics/`):
the examples are expected to move into package `semantics`, so `@! f` is that
package's `f`, `TestFunOk name` is "`name()` returns `true`" from
`semantics/Base.lean`, and the context is that section's variables
(`[GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hG : HeapGS hlc GF}
[go.Semantics] [semantics.Assumptions]`). A method `catcher.catch` is written
`@! catcher.catch` loosely; the real name is whatever goose's method naming gives.
-/

namespace Perennial.PendingLabelsRecover

/-! ## recover() in a function or method called by defer -/

-- A deferred method recovers 7 and stores it in the named result.
theorem methodRecover_spec :
    {{ (True : IProp GF) }} App (Val (@! methodRecover)) (Val #()) {{ RET #(W64 7); True }} := by sorry

-- A deferred top-level function recovers.
theorem topRecover_spec :
    {{ (True : IProp GF) }} App (Val (@! topRecover)) (Val #()) {{ RET #true; True }} := by sorry

-- Recover and re-panic: the inner function panics with 6 (5 + 1) ...
theorem repanicInner_spec (c : Loc) (s : w64) :
    ∀ Φ : val → IProp GF,
      (c.[catcher.t, "seen"] ↦ s) -∗
      ((c.[catcher.t, "seen"] ↦ (s + W64 1)) -∗ Φ (PanicV #(interface.mkOk go.uint64 #(W64 6)))) -∗
      WP (App (Val (@! repanicInner)) (Val #c)) {{ Φ }} := by sorry
-- ... which the caller's deferred literal recovers: 6*10 + 1.
theorem repanic_spec :
    {{ (True : IProp GF) }} App (Val (@! repanic)) (Val #()) {{ RET #(W64 61); True }} := by sorry

-- recover() is nil when not panicking; the function returns normally.
theorem recoverNotPanicking_spec :
    {{ (True : IProp GF) }} App (Val (@! recoverNotPanicking)) (Val #()) {{ RET #true; True }} := by sorry

-- `f := c.catch; defer f(&x)`: Go returns 9. Under the plan's proposal A this is
-- NOT expected to be provable (goose cannot see that `f` recovers, the ordinary
-- `catch` is stuck), which is sound. What must never be provable is the
-- "recover gave nil" behaviour, i.e. the panic escaping:
theorem methodValueRecover_go :   -- Go's behaviour; provable only with runtime panic state (plan's B)
    {{ (True : IProp GF) }} App (Val (@! methodValueRecover)) (Val #()) {{ RET #(W64 9); True }} := by sorry
/- MUST NOT be provable (it is false in Go):
   ∀ Φ, Φ (PanicV #(interface.mkOk go.uint64 #(W64 9))) ⊢
          WP (App (Val (@! methodValueRecover)) (Val #())) {{ Φ }}  -/

-- A direct, non-deferred call: Go's recover() returns nil and the call is a no-op.
-- Under proposal A (`recover()` in the ordinary `catch` is stuck) this is NOT
-- provable; that is the incompleteness decision point 6 accepts.
theorem directCall_go :
    {{ (True : IProp GF) }} App (Val (@! directCall)) (Val #()) {{ RET #true; True }} := by sorry

-- A deferred literal calling the recovering method: its recover() is nil in Go,
-- the panic continues and the outer literal recovers it (101). Also NOT
-- provable under proposal A (the direct `c.catch` call is stuck); it would be
-- with "nil in non-deferred F", which is unsound for `methodValueRecover`.
theorem helperInDeferredLiteral_go :
    {{ (True : IProp GF) }} App (Val (@! helperInDeferredLiteral)) (Val #()) {{ RET #(W64 101); True }} := by sorry

-- fmt shape: handleMethods with a String() that panics "oops" recovers via
-- `defer p.catchPanic(verb, "String")` and writes the PANIC message.
theorem printArg_bad_spec :
    {{ (True : IProp GF) }} App (Val (@! printArg)) (Val (#(interface.mkOk bad.t #()), #false))
    {{ RET (#true, #go!"%!v(PANIC=String method: oops)"); True }} := by sorry
theorem printArg_good_spec :
    {{ (True : IProp GF) }} App (Val (@! printArg)) (Val (#(interface.mkOk good.t #()), #false))
    {{ RET (#true, #go!"ok"); True }} := by sorry
-- With p.panicking, catchPanic re-panics with the same value, recovered by the caller.
theorem nestedPanic_spec :
    {{ (True : IProp GF) }} App (Val (@! nestedPanic)) (Val #()) {{ RET #go!"oops"; True }} := by sorry

/- The spec the deferred variant (`catcher.catch'deferred`, plan's proposal A)
   needs, in words: given the `$recover` cell holding a panic value
   `interface.mkOk go.uint64 #w`, the call stores `w` through `res`, increments
   `seen`, clears the cell (the panic is recovered), and returns `#()`; given the
   cell empty (not panicking), it changes nothing. The deferring function's
   `wrapDeferRecover` then returns its named result normally. -/

end Perennial.PendingLabelsRecover
