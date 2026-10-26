/-
The proof of `elimination_stack.NewLockedStack`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewLockedStack

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewLockedStack.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewLockedStack.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  iapply wp_fupd
  wp_apply wp_slice_make2 (V := GoString) (t := go.string) (W64 0) as %stack_sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  irename «$r0» => Hs
  generalize «$r0_ptr» = s at *
  iStructNamed Hs
  imod ghostVar_alloc ([] : List GoString) with ⟨%γ, Hγ⟩
  icases ghostVar_split γ ([] : List GoString) (1 : Qp).half (1 : Qp).half $$ [Hγ] with ⟨Hauth, Hfrag⟩
  · rw [Qp.half_add_half]; iexact Hγ
  imod sync.init_Mutex iprop(∃ (stack_sl : GoSlice) (stack : List GoString),
        "stack" ∷ s.[LockedStack, go!"stack"] ↦ stack_sl ∗
        "Hsl" ∷ stack_sl ↦* stack ∗
        "Hcap" ∷ ownSliceCap GoString stack_sl (DFrac.own 1) ∗
        "Hauth" ∷ ghostVar γ (1 : Qp).half stack.reverse) ⊤ (s.[LockedStack, go!"mu"])
    $$ [mu] [stack Hsl Hcap Hauth] with #Hmu
  · iexact mu
  · inext; iexists stack_sl, []; rw [List.reverse_nil]; iframe
  imodintro
  iapply HΦ
  unfold isLockedStack ownLockedStack
  iframe # ∗

end proof

end Perennial
