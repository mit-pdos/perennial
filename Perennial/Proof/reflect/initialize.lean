/-
The proof of `reflect.initialize'`.
-/
module

public import Perennial.Spec.reflect.initialize
public import Perennial.Spec.internal.gomodel.initialize
public import Perennial.Spec.internal.reflectcore.initialize
public import Perennial.Spec.iter.initialize
public import Perennial.Spec.strconv.initialize
public import Perennial.Spec.unsafe.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.initialize'.wp_proof
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG))
    (wp_reflectcore_initialize : internal.reflectcore.initialize'.spec (GF := GF) (hG := hG))
    (wp_iter_initialize : iter.initialize'.spec (GF := GF) (hG := hG))
    (wp_strconv_initialize : strconv.initialize'.spec (GF := GF) (hG := hG))
    (wp_unsafe_initialize : «unsafe».initialize'.spec (GF := GF) (hG := hG)) :
    reflect.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoSlice) kindNames (go.GoType.SliceType go.string) as Hk
  wp_apply wp_unsafe_initialize _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #_⟩
  wp_apply wp_strconv_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #_⟩
  wp_apply wp_iter_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #_⟩
  wp_apply wp_reflectcore_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #_⟩
  wp_apply wp_gomodel_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #_⟩
  -- kindNames
  wp_apply wp_slice_literal (V := GoString) (t := go.string) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  iapply wp_fupd
  wp_auto
  ipersist Hk
  ipersist Hsl
  iframe Hown
  is_pkg_init_finish
  isplitr
  · itrivial
  imodintro
  imodintro
  unfold reflect.isInit
  iexists _
  iframe Hk
  have key : ∀ (L : List GoString) (s : GoSlice), L = reflect.kindNamesVal →
      (s ↦*□ L : IProp GF) ⊢ s ↦*□ reflect.kindNamesVal := by
    intro L s h; rw [h]
  iapply key _ _ ?_ $$ Hsl
  simp [go.arrayLiteralSize, reflect.kindNamesVal, Int.max_def]

end proof

end Perennial
