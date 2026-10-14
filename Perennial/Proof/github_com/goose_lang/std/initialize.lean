/-
The proof of `github.com/goose-lang/std`'s `initialize'`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.initialize
public import Perennial.Spec.github_com.goose_lang.std.std_core.initialize
public import Perennial.Spec.github_com.goose_lang.primitive.initialize
public import Perennial.Spec.time.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.math.initialize

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.goose_lang.std.Assumptions]

theorem github_com.goose_lang.std.initialize'.wp_proof
    (wp_std_core_initialize' : github_com.goose_lang.std.std_core.initialize'.spec (GF := GF) (hG := hG))
    (wp_primitive_initialize' : github_com.goose_lang.primitive.initialize'.spec (GF := GF) (hG := hG))
    (wp_time_initialize' : time.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_initialize' : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_math_initialize' : math.initialize'.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.initialize'.spec (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_std_core_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown
    as ⟨Hown, #H1⟩
  wp_apply wp_primitive_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply wp_time_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply wp_sync_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H4⟩
  wp_apply wp_math_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H5⟩
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
