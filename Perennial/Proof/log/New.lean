/-
The proof of `log.New`.
-/
module

public import Perennial.Spec.log.New
public import Perennial.Spec.log.Logger__SetOutput
public import Perennial.Spec.log.Logger__SetPrefix
public import Perennial.Spec.log.Logger__SetFlags

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.New.wp_proof
    (wp_SetOutput : log.Logger.SetOutput.spec (GF := GF) (hG := hG))
    (wp_SetPrefix : log.Logger.SetPrefix.spec (GF := GF) (hG := hG))
    (wp_SetFlags : log.Logger.SetFlags.spec (GF := GF) (hG := hG)) :
    log.New.spec (GF := GF) (hG := hG) := by
  intro out pfx flag
  wp_start
  wp_auto
  irename flag => Hflag_arg
  irename «prefix» => Hprefix_arg
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  imod sync.init_Mutex iprop(∃ w : GoInterface, log.loggerOut (GF := GF) «$r0_ptr» ↦ w) ⊤
      (log.loggerOutMu (GF := GF) «$r0_ptr») $$ [outMu] [out] with #Hmu
  · iexact outMu
  · inext; iexists _; iexact out
  ihave Hdisc := (sync.atomic.ownBool_zero _ _).1 $$ isDiscard
  ihave Hpre := (sync.atomic.ownPointer_zero (T' := GoString) _ _).1 $$ prefix'
  ihave Hfl := (sync.atomic.ownInt32_zero _ _).1 $$ flag
  wp_apply wp_SetOutput «$r0_ptr» false out $$ [$Hmu $Hdisc] as ⟨%b, Hdisc⟩
  wp_apply wp_SetPrefix «$r0_ptr» null pfx $$ [$Hpre] as ⟨%p, Hpre, Hp⟩
  wp_apply wp_SetFlags «$r0_ptr» (W32 0) flag $$ [$Hfl] as Hfl
  iapply HΦ
  rw [log.ownLogger_unseal]; unfold log.ownLoggerDef
  iframe Hmu Hfl
  isplitr
  · ipureintro; exact Hnn
  isplitl [Hpre Hp]
  · iexists p; iframe
  iexists b; iexact Hdisc

end proof

end Perennial
