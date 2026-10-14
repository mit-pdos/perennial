/-
The proof of `github.com/goose-lang/primitive`'s `initialize'`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

theorem github_com.goose_lang.primitive.initialize'.wp_proof :
    github_com.goose_lang.primitive.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
