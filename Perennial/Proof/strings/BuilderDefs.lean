/-
Shared definitions of the proofs of the `strings.Builder` methods: `ownBuilder` (a builder and
the bytes it holds) and lemmas about it, and the triple of `lockBytes`, the loop of the model of
`Builder.String` (`Perennial/TrustedCode/strings.lean`).
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strings

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-! ## `strings.Builder` -/

/-- `b` points to a `strings.Builder` that holds the bytes `s` and is used through `b` (its
`addr`, which `copyCheck` sets to the receiver on first use, is `b` or not yet set). -/
def ownBuilder (b : Loc) (s : GoString) : IProp GF :=
  iprop(∃ (addr : Loc) (buf : GoSlice),
    b ↦ ({ addr' := addr, buf' := buf } : Builder) ∗ ⌜addr = null ∨ addr = b⌝ ∗
    buf ↦* s ∗ ownSliceCap w8 buf (DFrac.own 1))

/-- The receiver's type in the model of `Builder.String` (`TrustedCode/strings.lean`), which is
below `Builder.ty`'s definition. -/
theorem Builder_ty_eq : (go.GoType.Named go!"strings.Builder" [] : go.GoType) = Builder.ty := by
  unfold Builder.ty; rfl

/-- A zero `strings.Builder` (`var b strings.Builder`) holds no bytes. -/
theorem ownBuilder_zero (b : Loc) :
    b ↦ zero_val Builder ⊢ ownBuilder (GF := GF) b [] := by
  iintro Hb
  unfold ownBuilder
  iexists null, slice.nil
  iframe Hb
  isplitl []
  · ipureintro; exact Or.inl rfl
  isplitl []
  · iapply ownSlice_nil
  · iapply ownSliceCap_nil

/-- A byte's points-to, as a heap points-to. -/
theorem typedPointsto_w8_heap (l : Loc) (v : w8) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ heapPointsto l dq #v := by
  rw [typedPointsto_unseal_eq]
  iintro ⟨H, -⟩
  iapply (typedPointstoDef_w8 _ _ _).1 $$ H

/-- `lockBytes buf i` (`TrustedCode/strings.lean`), given the bytes of `buf` from index `i` on,
read-locks them and keeps them. -/
theorem Builder.wp_lockBytes (buf : GoSlice) (dq : DFrac) :
    ∀ (k : Nat) (i : w64) (vs : List w8), vs.length = k → 0 ≤ sint.Z i →
    sint.Z i + vs.length = sint.Z buf.len →
    {{ (arrayElems (GF := GF) (arrayIndexRef w8 (sint.Z i) buf.ptr) vs dq) }}
      (App (App (Val Builder.String.lockBytes) (Val #buf)) (Val #i))
    {{ RET #(); True }} := by
  intro k
  induction k with
  | zero =>
    intro i vs hk hi hlen
    iintro %Φ _ HΦ
    wp_call
    rw [decide_eq_false (by rw [List.length_eq_zero_iff.1 hk] at hlen; simp at hlen; omega)]
    wp_pures
    iapply HΦ; itrivial
  | succ k ih =>
    intro i vs hk hi hlen
    iintro %Φ Hl HΦ
    obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := by
      cases vs with
      | nil => simp at hk
      | cons v vs' => exact ⟨v, vs', rfl⟩
    simp only [List.length_cons] at hk hlen
    have hlt : sint.Z i < sint.Z buf.len := by omega
    wp_call
    rw [decide_eq_true hlt]
    wp_pures
    rw [ite_eq_left ⟨hi, hlt⟩]
    icases (arrayElems_cons _ v vs' _).1 $$ Hl with ⟨Hv, Hl⟩
    rw [go.arrayIndexRef_0]
    ihave Hv := typedPointsto_w8_heap _ _ _ $$ Hv
    simp only [sliceIndexRef]
    have hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
    have hrec := ih (i + W64 1) vs' (by omega) (by omega) (by push_cast at hlen; omega)
    rw [hi1, go.arrayIndexRef_add] at hrec
    wp_apply_core wp_start_read _ _ _ $$ Hv
    iintro ⟨-, -⟩
    wp_pures
    iapply hrec $$ Hl HΦ

/-- The bytes of `sl`, as element points-tos from its start. -/
theorem ownSlice_arrayElems (sl : GoSlice) (vs : List w8) (dq : DFrac) :
    (sl ↦*{dq} vs : IProp GF) ⊢ arrayElems (arrayIndexRef w8 0 sl.ptr) vs dq := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · obtain ⟨-, rfl⟩ := H
    unfold arrayElems; iapply BigSepL.bigSepL_nil.2; iempintro
  · rw [go.arrayIndexRef_0, typedPointsto_unseal]; unfold typedPointstoWrap
    simp only [TypedPointsto.typedPointstoDef]
    icases H with ⟨⟨-, H⟩, -⟩
    iexact H

end wps

end strings

end Perennial
end
