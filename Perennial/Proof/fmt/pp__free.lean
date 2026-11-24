/-
The proof of `fmt.(*pp).free`.
-/
module

public import Perennial.Spec.fmt.pp__free
public import Perennial.Spec.sync.Pool__Put
public import Perennial.Spec.sync.Pool__Get

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `fmt.pp.free.spec` for a printer whose address `p` and field address `p.fmt` are not
`nil`: `free` gives the printer back to the pool `ppFree`, whose `ppFreeElem` is a points-to of
the whole struct, `p ↦ v`, which holds `p ≠ null`; its field `fmt` is a struct too, so
reassembling it needs `p.fmt ≠ null`. `isPrinterAny` (field points-tos) holds neither. -/
theorem fmt.pp.free.wp_proof_of_ne_null
    (wp_Put : sync.Pool.Put.spec (GF := GF) (hG := hG)) :
    ∀ (p : Loc) (bs : GoString), p ≠ null → p.[fmt.pp, go!"fmt"] ≠ null →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ isPrinterAny p bs }}
      (App (Val (p @!! go.GoType.PointerType pp.ty @!! go!"free")) (Val #()))
    {{ RET #(); True }} := fun p bs hnn hfnn => by
  wp_start as Hp
  have hacc : isPkgInit (PROP := IProp GF) pkg_id.fmt ⊢ fmt.isInit (GF := GF) := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.fmt
  ihave #Hi := hacc $$ Hpkg
  unfold fmt.isInit
  icases Hi with ⟨%f, %hf, #Hpool⟩
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
  icases Hp with ⟨%F, %wid, %prec, %x, ⟨%bsl, Hb, Hbs, Hbcap⟩, Hfmt, Hib, Harg, ⟨%val, Hval⟩,
    ⟨%ro, Hro⟩, ⟨%ga, Hga⟩, Hpan, Herr, Hwrap, ⟨%wsl, %ws, Hw, Hws, Hwcap⟩⟩
  have h0 : sint.Z (W64 0) = 0 := rfl
  wp_auto
  ihave %hbwf := ownSliceCap_wf $$ Hbcap
  have h0' : sint.nat (W64 0) = 0 := rfl
  wp_if_destruct
  -- `cap(p.buf) > 64*1024`: `p.buf = nil`
  iclear Hbs Hbcap
  ihave Hbs := ownSlice_nil (V := w8) (DFrac.own 1)
  ihave Hbcap := ownSliceCap_nil (V := w8)
  rotate_left
  -- otherwise `p.buf = p.buf[:0]`
  rw [ite_eq_left_iff.mpr (by omega)]
  icases ownSlice_slice_with_cap (W64 0) (W64 0) bsl bs ⟨by omega, by omega, by omega⟩ $$ [Hbs Hbcap]
    with ⟨-, Hbs, Hbcap⟩
  · iframe
  simp only [subslice, h0', List.take_zero, List.drop_nil]
  wp_auto
  all_goals
    ihave %hwwf := ownSliceCap_wf $$ Hwcap
    wp_if_destruct
    -- `cap(p.wrappedErrs) > 8`: `p.wrappedErrs = nil`, and then `nil[:0]`
    iclear Hws Hwcap
    icases ownSlice_slice_with_cap (W64 0) (W64 0) slice.nil ([] : List w64)
      ⟨by omega, by omega, by decide⟩ $$ [] with ⟨-, Hws, Hwcap⟩
    · iframe
      isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    rotate_left
    -- `p.wrappedErrs[:0]`
    rw [ite_eq_left_iff.mpr (by omega)]
    icases ownSlice_slice_with_cap (W64 0) (W64 0) wsl ws ⟨by omega, by omega, by omega⟩ $$ [Hws Hwcap]
      with ⟨-, Hws, Hwcap⟩
    · iframe
    wp_auto
    all_goals
      simp only [subslice, h0', List.take_zero, List.drop_nil]
      unfold fmt.fmtOwn fmt.intbufOwn
      icases Hfmt with ⟨Hfb, HfF, Hfw, Hfp⟩
      icases Hib with ⟨%ib, Hib⟩
      wp_apply wp_Put $$ [-HΦ]
      · iframe #
        unfold fmt.ppFreeElem
        iexists p, (fmt.pp.mk _ GoInterface.nil _
          (fmt.fmt.mk p.[fmt.pp, go!"buf"] F wid prec ib) ro ga false false false _)
        isplitr
        · ipureintro; rfl
        isplitl [Hb Harg Hval Hfb HfF Hfw Hfp Hib Hro Hga Hpan Herr Hwrap Hw]
        · iapply typedPointsto_combine _ _ _ hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
          iapply typedPointsto_combine _ _ _ hfnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        dsimp only
        iframe
        try iframe #
      iapply HΦ
      itrivial

end proof

end Perennial
