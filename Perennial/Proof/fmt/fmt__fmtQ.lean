/-
The proof of `fmt.(*fmt).fmtQ`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtQ
public import Perennial.Spec.fmt.fmt__truncateString
public import Perennial.Spec.fmt.fmt__pad
public import Perennial.Spec.strconv.AppendQuote

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

omit package_sem in
/-- An array points-to at an equal length. -/
theorem fmt.fmtQ.array_len_cast {n m : Int} (h : n = m) (l : Loc) (arr : List w8) (dq : DFrac) :
    typedPointsto (GF := GF) l (array.mk n arr : GoArray w8 n) dq ⊢
      typedPointsto l (array.mk m arr : GoArray w8 m) dq := by
  subst h; exact .rfl

omit package_sem in
/-- The array `[68]byte` at `l` is the empty slice `l[:0]` with its capacity. -/
theorem fmt.fmtQ.array_to_slice0 (l : Loc) :
    (∃ ib : GoArray w8 68, typedPointsto l ib (DFrac.own 1) : IProp GF) ⊢
      slice.mk l (W64 0) (W64 68) ↦* ([] : List w8) ∗
        ownSliceCap w8 (slice.mk l (W64 0) (W64 68)) (DFrac.own 1) := by
  iintro ⟨%ib, H⟩
  obtain ⟨arr⟩ := ib
  icases typedPointsto_not_null_dup _ _ _ $$ H with ⟨H, %Hnn⟩
  rw [ownSlice_unseal, ownSliceCap_unseal]; unfold ownSliceDef ownSliceCapDef
  simp only [sliceIndexRef, show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 68) = 68 from rfl,
    go.arrayIndexRef_0, Int.sub_zero]
  isplitr [H]
  · iright
    isplit
    · iapply fmt.fmtQ.array_len_cast (n := 0) (m := sint.Z (W64 0)) rfl
      iapply array_empty _ _ Hnn
    · ipureintro; omega
  · iright
    isplit
    · ipureintro; omega
    · iexists array.mk _ arr
      iapply fmt.fmtQ.array_len_cast (n := 68) (by decide) $$ H

omit package_sem in
/-- The empty slice `l[:0]` with its capacity is the array `[68]byte` at `l`. -/
theorem fmt.fmtQ.slice0_to_array (l : Loc) (xs : List w8) :
    (slice.mk l (W64 0) (W64 68) ↦* xs ∗
        ownSliceCap w8 (slice.mk l (W64 0) (W64 68)) (DFrac.own 1) : IProp GF) ⊢
      ∃ ib : GoArray w8 68, typedPointsto l ib (DFrac.own 1) := by
  iintro ⟨-, H⟩
  rw [ownSliceCap_unseal]; unfold ownSliceCapDef
  simp only [sliceIndexRef, show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 68) = 68 from rfl,
    go.arrayIndexRef_0, Int.sub_zero]
  icases H with (%H | ⟨-, %ib, H⟩)
  · exact absurd H.2.2 (by decide)
  · obtain ⟨arr⟩ := ib
    iexists array.mk 68 arr
    iapply fmt.fmtQ.array_len_cast (m := 68) (by decide) $$ H

theorem fmt.fmt.fmtQ.wp_proof
    (wp_truncateString : fmt.fmt.truncateString.spec (GF := GF) (hG := hG))
    (wp_pad : fmt.fmt.pad.spec (GF := GF) (hG := hG))
    (wp_AppendQuote : strconv.AppendQuote.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtQ.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs s hsharp hplus hprecP hwid => by
  obtain ⟨wP, pP, mi, pl, sh, sp, ze, pV, sV⟩ := F
  simp only at hsharp hplus hprecP hwid ⊢
  subst hsharp hplus hprecP
  unfold fmt.intbufOwn
  wp_start as ⟨Hf, ⟨%ib, Hib⟩, Hbuf⟩
  ihave #Hstrconv : isPkgInit (PROP := IProp GF) pkg_id.strconv $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_truncateString _ _ _ _ _ s rfl $$ [$Hf] as Hf
  unfold fmt.fmtOwn
  icases Hf with ⟨Hbufp, Hflags, Hwid, Hprec⟩
  wp_auto
  rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 0 - W64 0 = W64 0 from rfl,
    show W64 68 - W64 0 = W64 68 from rfl]
  icases fmt.fmtQ.array_to_slice0 _ $$ [Hib] with ⟨Hsl, Hcap⟩
  · iexists ib; iexact Hib
  wp_apply wp_AppendQuote _ _ s $$ [$Hsl $Hcap] as %sl' ⟨%q, Hsl', Hcap', Hundo⟩
  wp_apply wp_pad f b (fmt.fmtFlags.mk wP false mi false false sp ze pV sV) wid prec bs sl' _
    (DFrac.own 1) (hwid.elim Or.inl (fun h => Or.inr (Or.inl h)))
    $$ [Hbufp Hflags Hwid Hprec Hbuf Hsl'] as ⟨Hown, Hbuf, Hsl'⟩
  · unfold fmt.fmtOwn; iframe
  ihave Hib := Hundo $$ [Hsl' Hcap']
  · iframe
  ihave Hib := fmt.fmtQ.slice0_to_array _ _ $$ Hib
  unfold fmt.fmtOwn
  iapply HΦ
  iexists _
  iframe

end proof

end Perennial
