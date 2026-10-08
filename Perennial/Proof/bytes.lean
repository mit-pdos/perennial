/-
Specs for the Go `bytes` package.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors
public import Perennial.Code.bytes
public import Perennial.GeneratedProof.bytes

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace bytes

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.bytes :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.bytes :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.bytes get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.bytes }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoArray w8 256) asciiSpace (go.ArrayType 256 go.uint8) as _
  repeat (wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (wp_apply errors.wp_New as %_ _)
  iframe Hown
  is_pkg_init_finish

theorem wp_Clone (sl_b : GoSlice) (dq : DFrac) (b : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗
       "Hsl_b" ∷ sl_b ↦*{dq} b }}
      (App (Val (@! Clone)) (Val #sl_b))
    {{ (sl_b' : GoSlice), RET #sl_b';
       "Hsl_b" ∷ sl_b ↦*{dq} b ∗
       "Hsl_b'" ∷ sl_b' ↦* b ∗
       "Hsl_b'_cap" ∷ ownSliceCap w8 sl_b' (DFrac.own 1) }} := by
  wp_start
  iNamed Hpre
  wp_auto
  by_cases Hif : sl_b = slice.nil
  · subst Hif
    simp only [decide_true]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl_b
    have hb : b = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; rfl)
    subst hb
    iapply HΦ
    iframe Hsl_b
    isplitl []
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  · simp only [decide_eq_false Hif]
    -- step to the slice literal without unfolding it (`wp_auto` would)
    wp_pure; wp_pure; wp_pure; wp_pure; wp_pure; wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) []
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, Hsl_cap⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) _ [] sl_b b dq $$ [Hsl Hsl_cap Hsl_b]
      with %s' ⟨Hs', Hs'_cap, Hsl_b⟩
    · iframe Hsl Hsl_cap Hsl_b
    rw [List.nil_append]
    iapply HΦ
    iframe Hs' Hs'_cap Hsl_b

theorem wp_Equal (sl_b0 sl_b1 : GoSlice) (d0 d1 : DFrac) (b0 b1 : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗
       "Hb0" ∷ sl_b0 ↦*{d0} b0 ∗
       "Hb1" ∷ sl_b1 ↦*{d1} b1 }}
      (App (App (Val (@! Equal)) (Val #sl_b0)) (Val #sl_b1))
    {{ RET #(decide (b0 = b1));
       sl_b0 ↦*{d0} b0 ∗
       sl_b1 ↦*{d1} b1 }} := by
  wp_start
  iNamed Hpre
  wp_auto
  wp_apply wp_bytes_to_string $$ Hb0 with Hb0
  wp_apply wp_bytes_to_string $$ Hb1 with Hb1
  iapply HΦ
  iframe

end wps

end bytes

end Perennial
end
