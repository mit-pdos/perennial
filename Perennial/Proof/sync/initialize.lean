/-
The proof of `sync.initialize'`.
-/
module

public import Perennial.Spec.sync.initialize
public import Perennial.Spec.internal.race.initialize
public import Perennial.Spec.internal.synctest.initialize
public import Perennial.Spec.sync.atomic.initialize

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.initialize'.wp_proof
    (wp_synctest_initialize : internal.synctest.initialize'.spec (GF := GF) (hG := hG))
    (wp_race_initialize : internal.race.initialize'.spec (GF := GF) (hG := hG))
    (wp_atomic_initialize : sync.atomic.initialize'.spec (GF := GF) (hG := hG)) :
    sync.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_synctest_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hsynctest⟩
  wp_apply wp_race_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hrace⟩
  wp_apply wp_atomic_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
