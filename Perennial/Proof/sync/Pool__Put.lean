/-
The proof of `sync.(*Pool).Put`, whose model (`TrustedCode/sync.lean`) gives `x` to the model
pool `Pool.state` finds.
-/
module

public import Perennial.Spec.sync.Pool__Put
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.pool.Pool__Put

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Pool.Put.wp_proof
    (wp_model_Put : github_com.mit_pdos.perennial.goose.model.pool.Pool.Put.spec (GF := GF) (hG := hG)) :
    sync.Pool.Put.spec (GF := GF) (hG := hG) := by
  intro p f P x
  wp_start as ⟨#His, Hx⟩
  cases x with
  | nil =>
    wp_auto
    iapply HΦ
    itrivial
  | ok i =>
    wp_auto
    wp_apply sync.wp_Pool_state p f P $$ [$His] as %s #Hs
    wp_apply wp_model_Put $$ [$Hs $Hx]
    iapply HΦ
    itrivial

end proof

end Perennial
