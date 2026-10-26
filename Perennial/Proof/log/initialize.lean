/-
The proof of `log.initialize'`.
-/
module

public import Perennial.Spec.log.initialize
public import Perennial.Spec.sync.initialize

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
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG)) :
    log.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := sync.Pool) bufferPool sync.Pool.ty as _
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  -- std: its trusted initializer does nothing
  wp_call
  -- bufferPool
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  -- init.0: its trusted model does nothing
  wp_func_call
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
