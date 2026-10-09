/-
`PureWp` instances for the exception
monad (`do:`, `return:`, `;;;`, `exceptionDo`), so that `wp_pures` steps
through function bodies.
-/
module

public import Perennial.Golang.Theory.PostLifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `exceptionSeq v executeVal` runs the
continuation `v`. -/
instance pure_execute_val (v : val) :
    PureWp (G := G) (L := L) True (App (App (Val exceptionSeq) (Val v)) (Val executeVal))
      (App (Val v) (Val #())) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionSeq_unseal, executeVal_unseal]
    simp only [executeValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_execute_val (v : val) :
    PureWp (G := G) (L := L) True (App (Val doExecute) (Val v)) (Val executeVal) where
  pure_wp_wp s E Φ K _ := by
    rw [doExecute_unseal, executeVal_unseal]
    simp only [executeValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_return_val (v1 v : val) :
    PureWp (G := G) (L := L) True (App (App (Val exceptionSeq) (Val v1)) (Val (returnVal v)))
      (Val (returnVal v)) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionSeq_unseal, returnVal_unseal]
    simp only [returnValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_do_return_val (v : val) :
    PureWp (G := G) (L := L) True (App (Val doReturn) (Val v)) (Val (returnVal v)) where
  pure_wp_wp s E Φ K _ := by
    rw [doReturn_unseal, returnVal_unseal]
    simp only [returnValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_exception_do_return_v (v : val) :
    PureWp (G := G) (L := L) True (App (Val exceptionDo) (Val (returnVal v))) (Val v) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionDo_unseal, returnVal_unseal]
    simp only [returnValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

instance pure_exception_do_execute_v :
    PureWp (G := G) (L := L) True (App (Val exceptionDo) (Val executeVal)) (Val #()) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionDo_unseal, executeVal_unseal]
    simp only [executeValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

end wps

end Perennial
