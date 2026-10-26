/-
The proof of `channel.HelloWorldSync`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldSync
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldSync.wp_proof
    (wp_HelloWorldAsync :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldSync.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_HelloWorldAsync as %ch %γ ⟨#Hch, #Hbag⟩
  wp_apply wp_bag_receive γ ch _ $$ Hbag as %v %Hv
  subst Hv
  wp_end

end proof

end Perennial
