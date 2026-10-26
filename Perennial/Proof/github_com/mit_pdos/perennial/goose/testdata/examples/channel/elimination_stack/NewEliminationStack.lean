/-
The proof of `elimination_stack.NewEliminationStack`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewEliminationStack
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewEliminationStack.wp_proof
    (wp_NewLockedStack :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewLockedStack.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.NewEliminationStack.spec
      (GF := GF) (hG := hG) := fun N => by
  wp_start
  wp_auto
  wp_apply wp_NewLockedStack as %base %γbase ⟨#Hbase, Hls⟩
  iapply wp_fupd
  wp_apply chan.wp_make1 (V := GoString) as %ch %γch ⟨#Hch, -, Hc⟩
  irename «$r0» => Hs
  generalize «$r0_ptr» = s at *
  ipersist Hs
  imod ghostVar_alloc ([] : List GoString) with ⟨%γspec, Hspec⟩
  icases ghostVar_split γspec ([] : List GoString) (1 : Qp).half (1 : Qp).half $$ [Hspec]
    with ⟨Hauth, Hes⟩
  · rw [Qp.half_add_half]; iexact Hspec
  imod ghostVar_alloc (0 : GName) with ⟨%γsn, Hsn⟩
  icases ghostVar_split γsn (0 : GName) (1 : Qp).half (1 : Qp).half $$ [Hsn] with ⟨Hsa, Hsf⟩
  · rw [Qp.half_add_half]; iexact Hsn
  imod ghostVar_alloc (0 : GName) with ⟨%γrn, Hrn⟩
  icases ghostVar_split γrn (0 : GName) (1 : Qp).half (1 : Qp).half $$ [Hrn] with ⟨Hra, Hrf⟩
  · rw [Qp.half_add_half]; iexact Hrn
  let γ : EliminationStackNames := ⟨γspec, γbase, γch, γsn, γrn⟩
  imod inv_alloc (N.@"inv") ⊤ (elimInv γ N) $$ [Hls Hauth Hc Hsa Hsf Hra Hrf] with #Hinv
  · inext
    unfold elimInv ownExchangerInv
    iexists [], .Idle
    iframe
    iexists 0, 0
    dsimp only [γ]
    iframe
    isplitl [Hsa]
    · iexact Hsa
    · iexact Hra
  imodintro
  iapply HΦ $$ %s %γ
  unfold isEliminationStack ownEliminationStack
  iframe
  iexists _
  iframe # ∗

end proof

end Perennial
