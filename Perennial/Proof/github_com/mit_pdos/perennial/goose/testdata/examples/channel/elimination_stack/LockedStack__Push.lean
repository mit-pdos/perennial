/-
The proof of `elimination_stack.(*LockedStack).Push`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack__Push
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Push.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Push.spec
      (GF := GF) (hG := hG) := fun v γ s => by
  wp_start as #His
  unfold isLockedStack
  iNamed His
  wp_auto
  wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  iNamed Hi
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) [v]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.string #v)] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := GoString) (t := go.string) stack_sl stack _ [v] (DFrac.own 1)
    $$ [Hsl Hcap Htmp] with %sl' ⟨Hsl, Hcap, -⟩
  · iframe
  iapply fupd_wp
  imod HΦ with ⟨%σ, Hl, HΦ⟩
  unfold ownLockedStack
  icombine Hl Hauth gives % ⟨_, Heq⟩
  subst Heq
  imod ghostVar_update_halves (v :: stack.reverse) γ _ _ $$ Hl Hauth with ⟨Hl, Hauth⟩
  imod HΦ $$ Hl with HΦ
  imodintro
  wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
  · inext; iexists sl', stack ++ [v]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    iframe
  iexact HΦ

end proof

end Perennial
