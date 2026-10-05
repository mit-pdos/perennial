/-
Port of `new/golang/theory/exception.v`: `PureWp` instances for the exception
monad (`do:`, `return:`, `;;;`, `exception_do`), so that `wp_pures` steps
through function bodies.
-/
import Perennial.Golang.Theory.PostLifting

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `exception_seq v executeVal` (Rocq `exception_seq v (executeVal)`) runs the
continuation `v`. -/
instance pure_execute_val (v : val) :
    PureWp (G := G) (L := L) True (App (App (Val exception_seq) (Val v)) (Val executeVal))
      (App (Val v) (Val #())) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_seq_unseal, executeVal_unseal]
    simp only [executeValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_execute_val (v : val) :
    PureWp (G := G) (L := L) True (App (Val do_execute) (Val v)) (Val executeVal) where
  pure_wp_wp s E Φ K _ := by
    rw [do_execute_unseal, executeVal_unseal]
    simp only [executeValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_return_val (v1 v : val) :
    PureWp (G := G) (L := L) True (App (App (Val exception_seq) (Val v1)) (Val (returnVal v)))
      (Val (returnVal v)) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_seq_unseal, returnVal_unseal]
    simp only [returnValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_return_val (v : val) :
    PureWp (G := G) (L := L) True (App (Val do_return) (Val v)) (Val (returnVal v)) where
  pure_wp_wp s E Φ K _ := by
    rw [do_return_unseal, returnVal_unseal]
    simp only [returnValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_exception_do_return_v (v : val) :
    PureWp (G := G) (L := L) True (App (Val exception_do) (Val (returnVal v))) (Val v) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_do_unseal, returnVal_unseal]
    simp only [returnValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_exception_do_execute_v :
    PureWp (G := G) (L := L) True (App (Val exception_do) (Val executeVal)) (Val #()) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_do_unseal, executeVal_unseal]
    simp only [executeValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

end wps

end Perennial
