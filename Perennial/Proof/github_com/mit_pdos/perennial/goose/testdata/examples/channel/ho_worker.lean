/-
The proof of `channel.ho_worker`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.ho_worker

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.ho_worker.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.ho_worker.spec
      (GF := GF) (hG := hG) := fun γ ch => by
  wp_start as #His
  unfold isRequestChan at *
  wp_auto
  ihave HI : (∃ r0 : request, "r" ∷ r_ptr ↦ r0 : IProp GF) $$ [r]
  · iexists _; iexact r
  wp_for HI
  wp_apply wp_bag_receive (t := request.ty) γ ch _ $$ His as %rq Hreq
  icases Hreq with ⟨%γfut, %Q, Hreq⟩
  unfold doRequest
  iNamed Hreq
  wp_bind (App (Val #rq.f') (Val #()))
  iapply wp_wand $$ Hf
  iintro %v ⟨%s, %Hv, HQ⟩
  subst Hv
  wp_auto
  wp_apply wp_future_fulfill (t := go.string) γfut rq.result' s $$ [$Hfut Hpromise HQ]
  · unfold Fulfilled; iexists Q; iframe
  wp_for_post
  iframe
  iexists rq
  iexact r

end proof

end Perennial
