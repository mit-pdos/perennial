/-
The specs of `with_defer:` and `with_defer_recover:`, of `panic(..)` and of
`recover()`.

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

/-- `with_defer: e`: the body runs with the cell `defer` of deferred functions,
whose chain then runs whatever the body's outcome; the outcome is then that of
the body (`exceptionDo`: the returned value, or stuck for a panic). -/
theorem wp_with_defer (e : Expr) (Φ : val → IProp GF) :
    iprop(∀ defer : Loc, defer ↦ func.mk BAnon BAnon #() -∗
      WP gl(let: "$ret" := subst "$defer" #defer e in
            (![deferType] #defer) #() ;; exceptionDo "$ret") {{ Φ }})
    ⊢ WP (App (Val wrapDefer) (Val (RecV BAnon (BNamed "$defer") e))) {{ Φ }} := by
  iintro Hwp
  wp_call
  wp_alloc defer as Hdefer
  wp_pures
  wp_store
  wp_pures
  iapply Hwp $$ Hdefer

/-- `with_defer_recover: r; e`: as `with_defer:`, with the `$panic` cell (`nil`),
set to the panic's value when the body's outcome is a panic (`panicVal p`,
`wp_panic`) before the deferred chain runs, and read and cleared by a
`recover()` (`wp_recoverPanic`); if the body panicked and the chain cleared the
cell, the function returns `r`, its results. `wp_auto` steps through the
checks once the body's outcome is a `returnVal`/`panicVal`. -/
theorem wp_with_defer_recover (r e : Expr) (Φ : val → IProp GF) :
    iprop(∀ defer : Loc, ∀ pnc : Loc, defer ↦ func.mk BAnon BAnon #() -∗
      pnc ↦ (interface.nil : GoInterface) -∗
      WP gl(let: "$ret" := subst "$panic" #pnc (subst "$defer" #defer e) in
            (if: (Fst "$ret") =⟨go.string⟩ #"panic" then #pnc <-[go.any] Snd "$ret" else #()) ;;
            (![deferType] #defer) #() ;;
            if: ((Fst "$ret") =⟨go.string⟩ #"panic") &&
                ((![go.any] #pnc) =⟨go.any⟩ #interface.nil)
            then (λ: <>, r : val) #()
            else exceptionDo "$ret") {{ Φ }})
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

/-- `panic(p)` (`p` an `interface{}`, to which Goose converts the argument), for
a non-nil `p = .ok i` (`panic(nil)` is stuck, `panic.impl`): its outcome is
`panicVal #p`, which ends the function body (`;;;` and the loops pass it on,
`pure_panic_val`, `wp_for_post_panic`). -/
theorem wp_panic (i : GoInterfaceOk) (Φ : val → IProp GF) :
    Φ (panicVal #(GoInterface.ok i)) ⊢
      WP (App (Val (@! go.panic)) (Val #(GoInterface.ok i))) {{ Φ }} := by
  iintro HΦ
  rw [func_unfold]
  unfold panic.impl
  wp_pures
  rw [panicVal_unseal]
  simp only [panicValDef]
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
