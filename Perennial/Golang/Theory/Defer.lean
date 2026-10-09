/-
The spec of `with_defer:`.

Note: `deferType` is an `abbrev` (unfolded by typeclass search) so that the
instances for function types apply to it.
-/
module

public import Perennial.Golang.Theory.TacticsSimp
public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Defn.Defer

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem wp_with_defer (e : Expr) (Φ : val → IProp GF) :
    iprop(∀ defer : Loc, defer ↦ func.mk BAnon BAnon #() -∗
      WP gl(let: "$func_ret" := exceptionDo (subst "$defer" #defer e) in
            (![deferType] #defer) #() ;; "$func_ret") {{ Φ }})
    ⊢ WP (App (Val wrapDefer) (Val (RecV BAnon (BNamed "$defer") e))) {{ Φ }} := by
  iintro Hwp
  wp_call
  wp_alloc defer as Hdefer
  wp_pures
  wp_store
  wp_pures
  iapply Hwp $$ Hdefer

end proof

end Perennial
