/-
The specs of `with_defer:` and `with_defer_recover:`.

Note: `deferType` is an `abbrev` (unfolded by typeclass search) so that the
instances for function types apply to it.
-/
module

public import Perennial.Golang.Theory.TacticsSimp
public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Defn.Defer

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `with_defer: e`: the body runs under a `Catch` whose handlers run the deferred
chain, then return the body's value (`wp_catch_val`) or raise its panic again
(`wp_catch_panic`). A body that does not panic needs no reasoning about the
`Catch`: `wp_auto` steps through it when the body returns. -/
theorem wp_with_defer (e : Expr) (Φ : val → IProp GF) :
    iprop(∀ defer : Loc, defer ↦ func.mk BAnon BAnon #() -∗
      WP (Catch (exceptionDo (subst "$defer" #defer e))
            gl(λ: "$p", (![deferType] #defer) #() ;; Raise "$p")
            gl(λ: "$func_ret", (![deferType] #defer) #() ;; "$func_ret")) {{ Φ }})
    ⊢ WP (App (Val wrapDefer) (Val (RecV BAnon (BNamed "$defer") e))) {{ Φ }} := by
  iintro Hwp
  wp_call
  wp_alloc defer as Hdefer
  wp_pures
  wp_store
  wp_pures
  iapply Hwp $$ Hdefer

/-- `with_defer_recover: r; e`: as `with_defer:`, with the `$panic` cell (`nil`)
that the handler sets to the panic's value before running the deferred chain, and
that a `recover()` (`wp_recoverPanic`) reads and clears; if the chain cleared it,
the function returns `r`, its results. -/
theorem wp_with_defer_recover (r e : Expr) (Φ : val → IProp GF) :
    iprop(∀ defer : Loc, ∀ pnc : Loc, defer ↦ func.mk BAnon BAnon #() -∗
      pnc ↦ (interface.nil : GoInterface) -∗
      WP (Catch (exceptionDo (subst "$panic" #pnc (subst "$defer" #defer e)))
            gl(λ: "$p",
              #pnc <-[go.any] "$p" ;;
              (![deferType] #defer) #() ;;
              let: "$p'" := ![go.any] #pnc in
              if: "$p'" =⟨go.any⟩ #interface.nil then (λ: <>, r : val) #() else Raise "$p'")
            gl(λ: "$func_ret", (![deferType] #defer) #() ;; "$func_ret")) {{ Φ }})
    ⊢ WP (App (App (Val wrapDeferRecover) (Val (RecV BAnon BAnon r)))
        (Val (RecV BAnon (BNamed "$defer") (Rec BAnon (BNamed "$panic") e)))) {{ Φ }} := by
  iintro Hwp
  wp_call
  wp_alloc defer as Hdefer
  wp_pures
  wp_store
  wp_pures
  wp_alloc pnc as Hpnc
  wp_pures
  iapply Hwp $$ Hdefer Hpnc

/-- `panic(p)` panics with `p` (an `interface{}`, to which Goose converts the
argument): the postcondition receives `PanicV #p`, which `wp_auto` (or
`wp_unwind`) takes through the caller's evaluation context up to a `Catch`. -/
theorem wp_panic (p : GoInterface) (Φ : val → IProp GF) :
    Φ (PanicV #p) ⊢ WP (App (Val (@! go.panic)) (Val #p)) {{ Φ }} := by
  iintro HΦ
  rw [func_unfold]
  unfold panic.impl
  wp_auto
  iexact HΦ

/-- `recover()` in a deferred function: it returns the value of the panic being
handled (`nil` if none) and clears it. -/
theorem wp_recoverPanic (pnc : Loc) (i : GoInterface) :
    {{ (pnc ↦ i : IProp GF) }} (App (Val recoverPanic) (Val #pnc))
    {{ RET #i; pnc ↦ (interface.nil : GoInterface) }} := by
  wp_start as Hpnc
  wp_auto
  iapply HΦ $$ Hpnc

end proof

end Perennial
