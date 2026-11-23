/-
The proof of `strings.Builder.String` (its trusted model, `TrustedCode/strings.lean`).
-/
module

public import Perennial.Spec.strings.Builder__String

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- A byte's typed points-to is its heap points-to (`typedPointsto_w8`). -/
theorem strings.w8_typedPointsto_heap (l : Loc) (b : w8) (dq : DFrac) :
    typedPointsto (GF := GF) l b dq ⊢ heapPointsto l dq #b := by
  rw [typedPointsto_unseal_eq]
  change iprop(heapPointsto l dq #b ∗ ⌜l ≠ null⌝) ⊢ _
  iintro ⟨H, -⟩
  iexact H

/-- The model's `Builder.readLock sl i` (a helper of `String`'s model): it leaves a reader on
each byte of `sl[i:]`, which needs only a persistent points-to of them. -/
theorem strings.wp_Builder_readLock (sl : GoSlice) (bs : List w8) :
    ⊢ (sl ↦*□ bs -∗ ∀ (i : w64) (Φ : val → IProp GF), ⌜0 ≤ sint.Z i⌝ -∗ Φ #() -∗
        WP (App (App (Val strings.Builder.readLock) (Val #sl)) (Val #i)) {{ Φ }}) := by
  iintro #Hsl
  unfold strings.Builder.readLock
  iloeb as IH
  iintro %i %Φ %Hi HΦ
  wp_pures
  wp_if_destruct
  · ihave %Hlen := ownSlice_len $$ Hsl
    obtain ⟨b, hb⟩ : ∃ b, bs[(sint.Z i).toNat]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    icases ownSlice_elem_acc (sint.Z i) b sl DFrac.discard bs Hi hb $$ Hsl with ⟨He, -⟩
    wp_pures
    rw [if_pos ⟨Hi, Hif⟩]
    ihave He := strings.w8_typedPointsto_heap _ _ _ $$ He
    wp_bind (StartRead _)
    wp_apply_core (wp_start_read (sliceIndexRef w8 (sint.Z i) sl) DFrac.discard #b) $$ He
    iintro -
    -- the `;;` (a lambda and its beta step), then `i + 1` (a pair and the addition), stopping
    -- before the recursive call, which is `IH`'s
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    iapply IH
    · ipureintro; word
    iexact HΦ
  · iapply HΦ

theorem strings.Builder.String.wp_proof :
    strings.Builder.String.spec (GF := GF) (hG := hG) := by
  intro l s
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%used, %buf, %dq, %Hnn, Haddr, Hbf, Hbuf, Hcap, %Hdq⟩
  imod ownSlice_persist $$ Hbuf with #Hbuf
  rw [show go.GoType.Named go!"strings.Builder" [] = strings.Builder.ty by with_unfolding_all rfl]
  wp_auto
  wp_apply wp_bytes_to_string buf s DFrac.discard $$ Hbuf as -
  -- leave a reader on each byte of `buf` (the model's `readLock`)
  wp_bind (App (App (Val strings.Builder.readLock) (Val #buf)) (Val #(W64 0)))
  ihave HL := strings.wp_Builder_readLock buf s $$ Hbuf
  iapply HL
  · ipureintro; decide
  wp_pures
  iapply HΦ
  iexists used, buf, DFrac.discard
  iframe Haddr Hbf Hbuf Hcap
  ipureintro; exact ⟨Hnn, DFrac.valid_discard⟩

end proof

end Perennial
