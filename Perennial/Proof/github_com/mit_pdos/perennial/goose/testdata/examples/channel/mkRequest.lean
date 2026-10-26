/-
The proof of `channel.mkRequest`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.mkRequest

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.mkRequest.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.mkRequest.spec
      (GF := GF) (hG := hG) := fun f Q => by
  wp_start as Hf
  wp_auto
  iapply wp_fupd
  wp_apply chan.wp_make2 (V := GoString) (W64 1) $$ [] as %ch %γ ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  imod start_future (V := GoString) ch γ (.Buffered []) (.inr rfl) $$ Hch Hown
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := GoString) γfut ch Q [] $$ Hfut HAwait with ⟨Hpromise, HAwait⟩
  rw [List.nil_append]
  imodintro
  iapply HΦ
  unfold doRequest awaitRequest
  iframe # ∗

end proof

end Perennial
