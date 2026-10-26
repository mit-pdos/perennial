/-
The proof of `channel.HigherOrderExample`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HigherOrderExample
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.ho_worker
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.mkRequest
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HigherOrderDefs

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

set_option maxHeartbeats 400000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.HigherOrderExample.wp_proof
    (wp_ho_worker :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.ho_worker.spec
        (GF := GF) (hG := hG))
    (wp_mkRequest :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.mkRequest.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.HigherOrderExample.spec
      (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  wp_apply chan.wp_make1 (V := request) $$ [] as %req_ch %γ ⟨#His, %Hcap, Hown⟩
  imod start_bag (fun r => iprop(∃ γfut Q, doRequest r γfut Q)) _ req_ch γ trivial $$ His Hown
    with #Hch
  ihave #Hreqs : isRequestChan γ req_ch $$ []
  · unfold isRequestChan; iexact Hch
  ipersist c
  wp_apply wp_fork $$ []
  · wp_apply wp_ho_worker $$ [$Hreqs]
    itrivial
  wp_apply wp_fork $$ []
  · wp_apply wp_ho_worker $$ [$Hreqs]
    itrivial
  wp_apply wp_mkRequest _ (fun s => iprop(⌜s = go!"hello world"⌝)) $$ [] as %γfut1 %r1 ⟨Hdo1, Hawait1⟩
  · wp_auto
    iexists _
    ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_mkRequest _ (fun s => iprop(⌜s = go!"HELLO"⌝)) $$ [] as %γfut2 %r2 ⟨Hdo2, Hawait2⟩
  · wp_auto
    iexists _
    ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_mkRequest _ (fun s => iprop(⌜s = go!"world"⌝)) $$ [] as %γfut3 %r3 ⟨Hdo3, Hawait3⟩
  · wp_auto
    iexists _
    ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_bag_send (t := request.ty) γ req_ch r1 _ $$ [$Hch Hdo1]
  · iexists _, _; iexact Hdo1
  wp_apply wp_bag_send (t := request.ty) γ req_ch r2 _ $$ [$Hch Hdo2]
  · iexists _, _; iexact Hdo2
  wp_apply wp_bag_send (t := request.ty) γ req_ch r3 _ $$ [$Hch Hdo3]
  · iexists _, _; iexact Hdo3
  wp_apply wp_get_response r1 γfut1 _ $$ Hawait1 as %s1 %Hs1
  wp_apply wp_get_response r2 γfut2 _ $$ Hawait2 as %s2 %Hs2
  wp_apply wp_get_response r3 γfut3 _ $$ Hawait3 as %s3 %Hs3
  subst Hs1 Hs2 Hs3
  wp_apply wp_slice_literal (V := GoString) [go!"hello world", go!"HELLO", go!"world"]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  imodintro
  iapply HΦ $$ Hsl

end proof

end Perennial
