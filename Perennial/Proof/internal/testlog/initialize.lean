/-
The proof of `internal.testlog.initialize'`.
-/
module

public import Perennial.Spec.internal.testlog.initialize
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
variable [package_sem : internal.testlog.Assumptions]

theorem internal.testlog.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG)) :
    internal.testlog.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := internal.testlog.«struct#03d5a6ce») _ _ as Hv
  iapply wp_fupd
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  iStructNamed Hv
  imod sync.init_Mutex _ ⊤ _ $$ mu [val] with #Hmu
  · inext; iexact val
  imodintro
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
