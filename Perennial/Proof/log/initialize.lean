/-
The proof of `log.initialize'`.
-/
module

public import Perennial.Spec.log.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.fmt.initialize
public import Perennial.Spec.internal.gomodel.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_fmt_initialize : fmt.initialize'.spec (GF := GF) (hG := hG))
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG)) :
    log.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := sync.Pool) bufferPool sync.Pool.ty as _
  wp_apply wp_sync_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply wp_fmt_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hfmt⟩
  wp_apply wp_gomodel_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hgm⟩
  -- std: its trusted initializer does nothing
  wp_call
  -- bufferPool
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  -- init.0: its Go model does nothing
  wp_func_call
  wp_auto
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
