/-
Port of `new/golang/theory/defer.v`: the spec of `with_defer:`.

Note: `deferType` is an `abbrev` (Rocq `Definition`, unfolded by typeclass
search) so that the instances for function types apply to it.
-/
import Perennial.Golang.Theory.Auto
import Perennial.Golang.Defn.Defer

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem wp_with_defer (e : expr) (Φ : val → IProp GF) :
    iprop(∀ defer : loc, defer ↦ func.mk BAnon BAnon #() -∗
      WP gl(let: "$func_ret" := exception_do (subst "$defer" #defer e) in
            (![deferType] #defer) #() ;; "$func_ret") {{ Φ }})
    ⊢ WP (App (Val wrap_defer) (Val (RecV BAnon (BNamed "$defer") e))) {{ Φ }} := by
  iintro Hwp
  wp_call
  wp_alloc defer as Hdefer
  wp_pures
  wp_store
  wp_pures
  iapply Hwp $$ Hdefer

end proof

end Perennial
