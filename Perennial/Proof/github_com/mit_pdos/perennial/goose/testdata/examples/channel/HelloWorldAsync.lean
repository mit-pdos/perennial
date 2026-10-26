/-
The proof of `channel.HelloWorldAsync`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.sys_hello_world

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync.wp_proof
    (wp_sys_hello_world :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.sys_hello_world.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.HelloWorldAsync.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := GoString) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  imod start_bag (fun (v : GoString) => iprop(⌜v = go!"Hello, World!"⌝)) _ ch γ trivial $$ Hch Hoc
    with #Hbag
  ipersist ch
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply wp_sys_hello_world
    wp_apply wp_bag_send γ ch _ _ $$ [$Hbag]
    · ipureintro; rfl
    itrivial
  iapply HΦ
  iframe #

end proof

end Perennial
