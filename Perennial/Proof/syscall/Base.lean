/-
Shared definitions of the proofs of `syscall`: its `isPkgInit` (no facts: the initializer only has
to run, which importing `os` needs), and the spec of the model `syscall.arbitraryStrings`.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Code.syscall
public import Perennial.GeneratedProof.syscall
public import Perennial.Proof.arbitraryString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace syscall

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- The package-initialized state: no facts (nothing proved here reads `syscall`'s variables). -/
abbrev isInit : IProp GF := iprop(True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.syscall :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.syscall :=
  build_get_is_pkg_init_wf

end init

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The model `syscall.arbitraryStrings` returns some slice of strings (owned, with its
capacity). -/
theorem wp_arbitraryStrings :
    {{ (True : IProp GF) }}
      (App (Val arbitraryStrings) (Val #()))
    {{ (s : GoSlice), RET #s; ∃ xs : List GoString,
        s ↦* xs ∗ ownSliceCap GoString s (DFrac.own 1) }} := by
  iintro %Φ - HΦ
  unfold arbitraryStrings
  wp_auto
  ihave HI : (∃ (sl : GoSlice) (xs : List GoString),
      "a" ∷ a_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* xs ∗
      "Hcap" ∷ ownSliceCap GoString sl (DFrac.own 1) : IProp GF) $$ [a]
  · iexists slice.nil, []
    iframe
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  wp_for HI
  wp_apply wp_ArbitraryInt as %c -
  wp_if_destruct
  · wp_apply fmt.wp_arbitraryString as %str -
    wp_apply wp_slice_literal (V := GoString) [str]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hsl Hcap Hsl2] with %sl' ⟨Hsl, Hcap, -⟩
    · iframe
    wp_for_post
    iframe
    iexists _, _
    iframe
  · have Hf : (!decide (c = W64 0)) = false := by
      revert Hif; cases (!decide (c = W64 0)) <;> simp
    rw [Hf]
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iexists _
    iframe

end wps

end syscall

end Perennial
