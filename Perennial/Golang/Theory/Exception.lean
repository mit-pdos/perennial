/-
`PureWp` instances for the exception
monad (`do:`, `return:`, `panic(..)`, `;;;`, `exceptionDo`), so that `wp_pures`
steps through function bodies, and the spec of an unrecovered panic at
`exceptionDo` (`wp_exceptionDo_panic`: stuck).
-/
module

public import Perennial.Golang.Theory.PostLifting

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
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

/-- `exceptionSeq v1 (panicVal p)` is `panicVal p`: a panic skips the rest of the
function body, like a `return:`. -/
instance pure_panic_val (v1 p : val) :
    PureWp (G := G) (L := L) True (App (App (Val exceptionSeq) (Val v1)) (Val (panicVal p)))
      (Val (panicVal p)) where
  pure_wp_wp s E Φ K _ := by
    rw [exceptionSeq_unseal, panicVal_unseal]
    simp only [panicValDef]
    iintro Hwp
    wp_call_lc Hlc
    iapply Hwp $$ Hlc

/-- The body of `go.panic`: `panic(p)` is the outcome `panicVal p`. -/
instance pure_panic_impl (p : val) :
    PureWp (G := G) (L := L) True (App (Val panic.impl) (Val p)) (Val (panicVal p)) where
  pure_wp_wp s E Φ K _ := by
    rw [panicVal_unseal]
    simp only [panicValDef]
    unfold panic.impl
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

/-- A panic that reaches `exceptionDo`, which no deferred function of the
function recovered, is stuck (as a run-time panic `Panic msg`, `wp_PanicOp`): a
proof shows that it does not happen. -/
theorem wp_exceptionDo_panic (p : val) (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) :
    ▷ False ⊢ WP (App (Val exceptionDo) (Val (panicVal p))) @ s; E {{ Φ }} := by
  rw [exceptionDo_unseal, panicVal_unseal]
  simp only [exceptionDoDef, panicValDef]
  iintro HF
  wp_call_lc Hlc
  iapply wp_PanicOp
  iexact HF

/-! The tags and payloads of the sealed outcomes, for the code that inspects an
outcome (`wrapDeferRecover`). -/

instance pure_fst_execute_val :
    PureWp (G := G) (L := L) True (Fst (Val executeVal)) (Val #go!"execute") := by
  rw [executeVal_unseal]; simp only [executeValDef]; infer_instance

instance pure_fst_return_val (v : val) :
    PureWp (G := G) (L := L) True (Fst (Val (returnVal v))) (Val #go!"return") := by
  rw [returnVal_unseal]; simp only [returnValDef]; infer_instance

instance pure_fst_panic_val (p : val) :
    PureWp (G := G) (L := L) True (Fst (Val (panicVal p))) (Val #go!"panic") := by
  rw [panicVal_unseal]; simp only [panicValDef]; infer_instance

instance pure_snd_panic_val (p : val) :
    PureWp (G := G) (L := L) True (Snd (Val (panicVal p))) (Val p) := by
  rw [panicVal_unseal]; simp only [panicValDef]; infer_instance

end wps

end Perennial
