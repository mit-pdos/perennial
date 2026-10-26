/-
The proof of `channel.simple_multi_join`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.simple_multi_join

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.simple_multi_join.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.simple_multi_join.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := Unit) $$ [] as %ch %γ ⟨#Hch, -, Hoc⟩
  · ipureintro; decide
  imod start_future (V := Unit) ch γ _ (.inr rfl) $$ Hch Hoc
    with ⟨%γfut, #Hfut, HAwait⟩
  imod future_alloc_promise (V := Unit) γfut ch
    (fun _ => iprop(hello_ptr ↦ go!"Hello")) [] $$ Hfut HAwait with ⟨Hpromise1, HAwait⟩
  imod future_alloc_promise (V := Unit) γfut ch
    (fun _ => iprop(world_ptr ↦ go!"World")) _ $$ Hfut HAwait with ⟨Hpromise2, HAwait⟩
  ipersist ch
  wp_apply wp_fork $$ [Hpromise1 hello]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.GoType.StructType []) γfut ch () $$ [$Hfut Hpromise1 hello]
    · unfold Fulfilled; iexists _; iframe; iassumption
    itrivial
  wp_apply wp_fork $$ [Hpromise2 world]
  · wp_auto
    wp_apply wp_future_fulfill (t := go.GoType.StructType []) γfut ch () $$ [$Hfut Hpromise2 world]
    · unfold Fulfilled; iexists _; iframe; iassumption
    itrivial
  wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
    as %v1 %P1 %pre1 %post1 ⟨%Hsplit1, HP1, HAwait⟩
  -- which contract was fulfilled first
  rcases pre1 with _ | ⟨_, _ | ⟨_, pre1⟩⟩
  · simp only [List.nil_append] at Hsplit1
    obtain ⟨rfl, rfl⟩ := Hsplit1
    wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
      as %v2 %P2 %pre2 %post2 ⟨%Hsplit2, HP2, -⟩
    rcases pre2 with _ | ⟨_, pre2⟩
    · simp only [List.nil_append] at Hsplit2
      obtain ⟨rfl, -⟩ := Hsplit2
      wp_auto
      simp only [List.cons_append, List.nil_append]
      wp_end
    · simp at Hsplit2
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at Hsplit1
    obtain ⟨rfl, rfl, rfl⟩ := Hsplit1
    wp_apply wp_future_await (t := go.GoType.StructType []) γfut ch _ $$ [$Hfut $HAwait]
      as %v2 %P2 %pre2 %post2 ⟨%Hsplit2, HP2, -⟩
    rcases pre2 with _ | ⟨_, pre2⟩
    · simp only [List.nil_append] at Hsplit2
      obtain ⟨rfl, -⟩ := Hsplit2
      wp_auto
      simp only [List.cons_append, List.nil_append]
      wp_end
    · simp at Hsplit2
  · simp at Hsplit1

end proof

end Perennial
