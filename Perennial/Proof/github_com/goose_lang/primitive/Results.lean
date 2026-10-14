/-
Corollaries of the linked results of `github.com/goose-lang/primitive`: the
specializations `wp_Assume_true`/`wp_Assume_false` of `wp_Assume`.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.goose_lang.primitive

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

theorem wp_Assume_true (Φ : val → IProp GF) :
    ⊢ Φ #() -∗ WP (App (Val (@! Assume)) (Val #true)) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_Assume as %_
  iexact HΦ

theorem wp_Assume_false :
    ⊢ ∀ Φ : val → IProp GF, WP (App (Val (@! Assume)) (Val #false)) {{ Φ }} := by
  iintro %Φ
  wp_apply wp_Assume as %H
  cases H

end results

end github_com.goose_lang.primitive

end Perennial
