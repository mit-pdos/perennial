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
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `exception_seq v execute_val` (Rocq `exception_seq v (execute_val)`) runs the
continuation `v`. -/
instance pure_execute_val (v : val) :
    PureWp (G := G) (L := L) True (App (App (Val exception_seq) (Val v)) (Val execute_val))
      (App (Val v) (Val #())) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_seq_unseal, execute_val_unseal]
    simp only [execute_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_execute_val (v : val) :
    PureWp (G := G) (L := L) True (App (Val do_execute) (Val v)) (Val execute_val) where
  pure_wp_wp s E Φ K _ := by
    rw [do_execute_unseal, execute_val_unseal]
    simp only [execute_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_return_val (v1 v : val) :
    PureWp (G := G) (L := L) True (App (App (Val exception_seq) (Val v1)) (Val (return_val v)))
      (Val (return_val v)) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_seq_unseal, return_val_unseal]
    simp only [return_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_return_val (v : val) :
    PureWp (G := G) (L := L) True (App (Val do_return) (Val v)) (Val (return_val v)) where
  pure_wp_wp s E Φ K _ := by
    rw [do_return_unseal, return_val_unseal]
    simp only [return_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_exception_do_return_v (v : val) :
    PureWp (G := G) (L := L) True (App (Val exception_do) (Val (return_val v))) (Val v) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_do_unseal, return_val_unseal]
    simp only [return_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_exception_do_execute_v :
    PureWp (G := G) (L := L) True (App (Val exception_do) (Val execute_val)) (Val #()) where
  pure_wp_wp s E Φ K _ := by
    rw [exception_do_unseal, execute_val_unseal]
    simp only [execute_val_def]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

end wps

end Perennial
