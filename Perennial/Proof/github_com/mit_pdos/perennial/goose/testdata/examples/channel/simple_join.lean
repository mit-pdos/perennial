/-
The proof of `channel.simple_join`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.simple_join

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.simple_join.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.simple_join.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Unit) ch γ _ (.inr rfl) $$ Hch Hoc
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Unit) γfut ch
    (fun _ => iprop(message_ptr ↦ go!"Hello, World!")) [] $$ Hfut HAwait with ⟨Hpromise, HAwait⟩
  ipersist ch
  wp_apply wp_fork $$ [Hpromise message]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.GoType.StructType []) γfut ch () $$ [$Hfut Hpromise message]
    · unfold Fulfilled; iexists _; iframe; iassumption
    itrivial
  wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
    as %v %P %pre %post ⟨%Hsplit, HP, -⟩
  rcases pre with _ | ⟨_, pre⟩
  · simp only [List.nil_append, List.cons.injEq] at Hsplit
    obtain ⟨rfl, -⟩ := Hsplit
    wp_auto
    wp_end
  · simp at Hsplit

end proof

end Perennial
