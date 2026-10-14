/-
The proof of `elimination_stack.(*LockedStack).Pop`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack__Pop
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Pop.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Pop.spec
      (GF := GF) (hG := hG) := fun γ s => by
  wp_start as #His
  unfold isLockedStack
  iNamed His
  wp_auto
  wp_apply wp_Mutex_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  iNamed Hi
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
  iapply fupd_wp
  imod HΦ with ⟨%σ, Hl, HΦ⟩
  unfold ownLockedStack
  icombine Hl Hauth gives % ⟨_, Heq⟩
  obtain rfl : stack = σ.reverse := by rw [Heq, List.reverse_reverse]
  rcases σ with _ | ⟨v, σ⟩
  · imod HΦ $$ Hl with HΦ
    imodintro
    wp_if_destruct
    · wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
      · inext; iexists stack_sl, []; simp only [List.reverse_nil]; iframe
      iexact HΦ
    · exfalso; simp at Hlen; word
  · imod ghostVar_update_halves σ γ _ _ $$ Hl Hauth with ⟨Hl, Hauth⟩
    imod HΦ $$ Hl with HΦ
    imodintro
    simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton] at Hlen
    wp_if_destruct
    · exfalso; word
    have hpos : 0 ≤ sint.Z (stack_sl.len - W64 1) := by word
    rw [ite_eq_left (show 0 ≤ sint.Z (stack_sl.len - W64 1) ∧ sint.Z (stack_sl.len - W64 1) < sint.Z stack_sl.len by word)]
    rw [List.reverse_cons]
    wp_apply wp_load_slice_index stack_sl (sint.Z (stack_sl.len - W64 1)) (σ.reverse ++ [v]) _ v hpos
      $$ [Hsl] with Hsl
    · iframe; ipureintro
      have hidx : (sint.Z (stack_sl.len - W64 1)).toNat = σ.reverse.length := by
        simp only [List.length_reverse]; word
      rw [hidx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (stack_sl.len - W64 1) ∧
      sint.Z (stack_sl.len - W64 1) ≤ sint.Z stack_sl.cap by word)]
    icases ownSlice_slice_with_cap (W64 0) (stack_sl.len - W64 1) stack_sl (σ.reverse ++ [v])
      (by word) $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
    · iframe
    wp_auto
    wp_apply wp_Mutex_Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
    · inext; iexists _, σ.reverse
      have hn : sint.nat (stack_sl.len - W64 1) = σ.reverse.length := by
        simp only [List.length_reverse]; word
      rw [List.reverse_reverse, hn, show sint.nat (W64 0) = 0 from rfl]
      simp only [subslice, List.drop_zero, List.take_left']
      iframe
    iexact HΦ

end proof

end Perennial
