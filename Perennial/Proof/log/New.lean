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
  irename out => Hout_arg
  irename «prefix» => Hprefix_arg
  icases «$r0_al» with %Hal
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hl, %Hnn⟩
  have Hla := log.LoggerAligned_of (GF := GF) _ Hnn Hal
  iStructNamed Hl
  imod sync.init_Mutex iprop(∃ w : GoInterface, log.outField (GF := GF) «$r0_ptr» ↦ w) ⊤
      (log.outMuField (GF := GF) «$r0_ptr») $$ [outMu] [out] with #Hmu
  · iexact outMu
  · inext; iexists _; iexact out
  ihave Hdisc : sync.atomic.ownBool (GF := GF) (log.isDiscardField (GF := GF) «$r0_ptr»)
      (DFrac.own 1) false $$ [isDiscard]
  · rw [sync.atomic.ownBool_unseal]; unfold sync.atomic.ownBoolDef
    rw [show ({ _0' := zero_val _, v' := sync.atomic.b32w false } : sync.atomic.Bool') =
      zero_val _ from rfl]
    iexact isDiscard
  ihave Hpre : sync.atomic.ownPointer (GF := GF) (T' := GoString)
      (log.prefixField (GF := GF) «$r0_ptr») (DFrac.own 1) null $$ [prefix']
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; iexact prefix'
  ihave Hfl : sync.atomic.ownInt32 (GF := GF) (log.flagField (GF := GF) «$r0_ptr»)
      (DFrac.own 1) (W32 0) $$ [flag]
  · rw [sync.atomic.ownInt32_unseal]; unfold sync.atomic.ownInt32Def
    rw [show ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) = zero_val _ from rfl]
    iexact flag
  wp_apply wp_SetOutput «$r0_ptr» false out $$ [$Hmu $Hdisc] as ⟨%b, Hdisc⟩
  · ipureintro; exact Hla
  wp_apply wp_SetPrefix «$r0_ptr» null pfx $$ [$Hpre] as ⟨%p, Hpre, Hp⟩
  · ipureintro; exact Hla
  wp_apply wp_SetFlags «$r0_ptr» (W32 0) flag $$ [$Hfl] as Hfl
  · ipureintro; exact Hla
  iapply HΦ
  unfold log.ownLogger
  iframe Hmu Hfl
  isplitr
  · ipureintro; exact Hnn
  isplitr
  · ipureintro; exact Hla
  isplitl [Hpre Hp]
  · iexists p; iframe
  iexists b; iexact Hdisc

end proof

end Perennial
