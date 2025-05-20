From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.base_logic.lib Require Import invariants.
From Perennial.program_logic Require Import weakestpre.
From iris.base_logic Require Export lib.ghost_var.

(* From Perennial.goose_lang Require Import lang typing. *)
From Perennial.goose_lang Require Import proofmode notation.
(* From Perennial.goose_lang Require Import persistent_readonly. *)
From Perennial.goose_lang.lib Require Export waitgroup.impl.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang.lib Require Export lock.
From Perennial.Helpers Require Import NamedProps.


From Perennial.algebra Require Import map.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

(*
  XXX:
  The waitgroup docs/comments stresses the fact that "the first WaitGroup.Add
  must be synchronized with WaitGroup.Wait". Why? I can't tell if it's a
  liveness issue, or safety. One conservative model would have a "positive" and
  a "negative" counter. Negative is increased each time Done() is called, and
  positive is increased when Add() is called. We can make access to the positive
  integer unguarded by a mutex, so concurrent Add() and Wait() is disallowed.
  This is overly conservative, since concurrent Add()s are also disallowed, as
  are concurrent Add() and Wait() when the counter is guaranteed to not be 0,
  which is allowed to happen.
 *)

Section proof.

  Class waitgroupG Σ := {
      #[global] wg_tokG :: mapG Σ u64 unit;
      #[global] wg_totalG :: ghost_varG Σ u64; (* TODO: this will need to be mnat *)
      #[global] wg_doneTokG :: inG Σ (exclR unitO)
  }.
  Definition waitgroupΣ := #[mapΣ u64 unit ; ghost_varΣ u64 ; GFunctor (exclR unitO)].
  Global Instance subG_waitgroupΣ {Σ} : subG (waitgroupΣ) Σ → (waitgroupG Σ).
  Proof. solve_inG. Qed.

  Context `{!heapGS Σ} (N : namespace).
  Context `{!waitgroupG Σ}.

  Record waitgroup_names :=
    mkwaitgroup_names {
      tok_gn:gname;
      total_gn:gname;
      done_gn:gname
    }.

  Implicit Type γ:waitgroup_names.

  Definition own_WaitGroup_token γ (i:u64) : iProp Σ := i ⤳[γ.(tok_gn)] ().

  Definition is_WaitGroup wg γ P : iProp Σ :=
    ∃ lk (vptr:loc),
      ⌜wg = (lk, #vptr)%V⌝ ∗
      is_lock N lk (
        ∃ (remaining:gset u64) (total:u64),
          "%Hremaining" ∷ ⌜(∀ r, r ∈ remaining → uint.nat r < uint.nat total)⌝ ∗
          "Htotal" ∷ ghost_var γ.(total_gn) (1/2) total ∗
          "Hv" ∷ vptr ↦[uint64T] #(size remaining) ∗
          "Htoks" ∷ ([∗ set] i ∈ (fin_to_set u64), ⌜i ∈ remaining⌝ ∨ own_WaitGroup_token γ i) ∗
          "HP" ∷ (own γ.(done_gn) (Excl ())
                  (* If this done token in this invariant, then the user has
                     called Wait() once and lacks the resources to do so again. *)
                  ∨ [∗ set] i ∈ (fin_to_set u64), ⌜ uint.nat total ≤ uint.nat i ⌝ ∨ ⌜i ∈ remaining⌝ ∨ (P i))

      ).

  (* XXX: here, wg is a value. Maybe it should be a loc? *)
  Definition own_WaitGroup (wg:val) γ (n:u64) (P:u64 → iProp Σ) : iProp Σ :=
      own γ.(done_gn) (Excl ()) ∗
      ghost_var γ.(total_gn) (1/2) n ∗
      is_WaitGroup wg γ P.

  Definition own_free_WaitGroup (wg:val) : iProp Σ :=
    ∃ (mu:loc) (vptr:loc),
      ⌜wg = (#mu, #vptr)%V⌝ ∗
      is_free_lock mu ∗
      vptr ↦[uint64T] #0
  .

Lemma wp_NewWaitGroup_free :
  {{{
      True
  }}}
    waitgroup.New #()
  {{{
        (wg:val), RET wg; own_free_WaitGroup wg
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_rec. wp_pures.
  wp_apply (wp_new_free_lock).
  iIntros (lk) "His_lock".
  wp_apply (wp_ref_to).
  { naive_solver. }
  iIntros (vptr) "Hv".
  wp_pures.
  iApply "HΦ".
  iExists _, _.
  iFrame.
  done.
Qed.

Lemma own_WaitGroup_to_is_WaitGroup wg γ P n :
  own_WaitGroup wg γ n P -∗ is_WaitGroup wg γ P.
Proof.
  iIntros "(_ & _ & $)".
Qed.

Lemma free_WaitGroup_alloc wg P :
  own_free_WaitGroup wg ={↑N}=∗ (∃ γ, own_WaitGroup wg γ 0 P ).
Proof.
  iIntros "Hwg".
  iDestruct "Hwg" as (??) "(%Hwg & His_lock & Hv)".
  iMod (ghost_map_alloc_fin ()) as (γtok) "Htokens".
  iMod (ghost_var_alloc (W64 0)) as (γtotal) "[Htotal Ht2]".
  iMod (own_alloc (Excl ())) as (γdone) "Hdone".
  { done. }
  iExists (mkwaitgroup_names γtok γtotal γdone).
  iFrame.
  iExists _, _.
  iSplitL ""; first done.
  simpl.

  iMod (alloc_lock with "His_lock [-]") as "$"; last done.
  iNext.
  iExists ∅, (W64 0).
  rewrite size_empty.
  iFrame "Hv Htotal".
  iSplitL "".
  {
    iPureIntro.
    set_solver.
  }
  iSplitR "".
  {
    iApply (big_sepS_impl with "Htokens").
    iModIntro.
    iIntros.
    iRight.
    iFrame.
  }
  {
    iDestruct (big_sepS_emp with "[]") as "Htriv"; first done.
    iRight. iApply (big_sepS_impl with "Htriv").
    iModIntro.
    iIntros.
    iLeft.
    iPureIntro.
    word.
  }
Qed.

Lemma wp_NewWaitGroup (P:u64 → iProp Σ) :
  {{{
      True
  }}}
    waitgroup.New #()
  {{{
        (wg:val) γ, RET wg; own_WaitGroup wg γ 0 P
  }}}
.
Proof.
  iIntros (Φ) "_ HΦ".
  iApply wp_fupd.
  wp_apply (wp_NewWaitGroup_free).
  iIntros (?) "Hwg".
  iMod (fupd_mask_subseteq (↑N)) as "Hmask".
  { set_solver. }
  iMod (free_WaitGroup_alloc with "Hwg") as (?) "Hwg".
  iMod "Hmask".
  iApply "HΦ".
  by iFrame.
Qed.

Local Opaque load_ty store_ty.

Lemma u64_set_size_all_lt (W : gset u64) (n : nat) :
 (∀ s : u64, s ∈ W → uint.nat s < n)%Z → (size W ≤ n)%Z.
Proof.
  revert W.
  induction n as [| n IHn] => W Hvalid.
  - destruct W as [| x W] using set_ind_L; auto.
    { rewrite size_empty. lia. }
    exfalso. opose proof (Hvalid x _); first by set_solver. lia.
  - transitivity (size ({[W64 n]} ∪ (W ∖ {[W64 n]}))).
    { apply Nat2Z.inj_le. apply subseteq_size. set_unfold. intros x. destruct (decide (x = W64 n)); auto. }
    rewrite size_union ?size_singleton; last by set_solver.
    refine (_ (IHn (W ∖ {[W64 n]}) _)); first lia.
    { set_unfold. intros x (Hin&Hneq). opose proof (Hvalid x _); auto.
      cut (uint.nat x ≠ n); first lia.
      intros Heq.
      move: Hneq.
      rewrite -Heq.
      rewrite Z2Nat.id; last by word.
      rewrite /W64 word.of_Z_unsigned. auto.
    }
Qed.

Lemma wp_WaitGroup__Add wg γ n P :
uint.nat (word.add n 1) > uint.nat n →
  {{{
      own_WaitGroup wg γ n P
  }}}
    waitgroup.Add wg #1
  {{{
        RET #(); own_WaitGroup wg γ (word.add n 1) P ∗ own_WaitGroup_token γ n
  }}}.
Proof.
  intros Hoverflow.
  iIntros (Φ) "Hwg HΦ".
  wp_rec. wp_pures.
  iDestruct "Hwg" as "(Hdone & Htotal1 & #His)".
  iDestruct "His" as (??) "(%HwgPair & Hlk)".
  rewrite HwgPair.
  wp_pures.
  wp_apply (wp_Mutex__Lock with "Hlk").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  iDestruct "HP" as "[Hbad|HP]".
  { iCombine "Hdone Hbad" gives %H. exfalso. naive_solver. }
  iDestruct (ghost_var_agree with "Htotal1 Htotal") as %->.
  iMod (ghost_var_update_2 (word.add total 1) with "Htotal1 Htotal") as "[Htotal1 Htotal]".
  { by apply Qp.half_half. }
  wp_load.
  wp_store.
  iDestruct (big_sepS_elem_of_acc_impl total with "Htoks") as "[Htok Htoks]".
  { set_solver. }

  iDestruct "Htok" as "[%Hbad | Htok]".
  {
    exfalso.
    apply Hremaining in Hbad.
    word.
  }
  iApply (wp_Mutex__Unlock with "[$Hlocked $Hlk Htotal HP Htoks Hv]").
  {
    iNext.
    iExists (remaining ∪ {[total]}).
    iExists (word.add total 1).
    iSplitL "".
    {
      iPureIntro.
      intros.
      rewrite elem_of_union in H.
      destruct H as [|].
      { apply Hremaining in H. word. }
      { replace (r) with (total) by set_solver. word. }
    }
    iFrame "Htotal".
    iSplitL "Hv".
    {
      replace ((word.add 1 (size remaining))) with (W64 (size (remaining ∪ {[total]}))); last first.
      {
        rewrite size_union; last first.
        { set_unfold. intros x' Hin Heq. specialize (Hremaining x' Hin). subst. lia. }
        rewrite size_singleton.
        apply u64_set_size_all_lt in Hremaining. word.
      }
      done.
    }
    iSplitL "Htoks".
    {
      iApply "Htoks".
      {
        iModIntro.
        iIntros (???) "[%H1|H2]".
        {
          iLeft.
          iPureIntro.
          set_solver.
        }
        iRight.
        done.
      }
      {
        iLeft.
        iPureIntro.
        set_solver.
      }
    }

    iRight.
    iApply (big_sepS_impl with "HP").
    iModIntro.
    iIntros (??) "[%H1|[%H2|H3]]".
    {
      destruct (decide (uint.nat total = uint.nat x)).
      {
        replace (x) with (total) by word.
        iRight. iLeft. iPureIntro. set_solver.
      }
      { iLeft. word. }
    }
    {
      iRight.
      iLeft.
      iPureIntro.
      set_solver.
    }
    iFrame.
  }
  iNext.
  iIntros.
  iApply "HΦ".
  iFrame "Htok".
  iFrame.
  iExists _, _; iFrame "#∗".
  done.
Qed.

Lemma wp_WaitGroup__Done wg γ P n :
  {{{
      is_WaitGroup wg γ P ∗ own_WaitGroup_token γ n ∗ P n
  }}}
    waitgroup.Done wg
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros (Φ) "(#Hwg & Htok & HPn) HΦ".
  wp_rec. wp_pures.
  iDestruct "Hwg" as (??) "(%HwgPair & Hlk)".
  rewrite HwgPair.
  wp_pures.

  wp_apply (wp_Mutex__Lock with "Hlk").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  wp_load.
  wp_store.

  iApply (wp_Mutex__Unlock with "[$Hlocked $Hlk Htotal HP Htoks Hv Htok HPn]").
  {
    iNext.
    iExists (remaining ∖ {[n]}), total.
    iSplitL "".
    { iPureIntro. intros. apply Hremaining. set_solver. }
    iFrame.
    iDestruct (big_sepS_elem_of_acc_impl n with "Htoks") as "[HH Htoks]".
    { set_solver. }
    iDestruct "HH" as "[%HnRemaining | Hbad]"; last first.
    {
      iDestruct (ghost_map_points_to_valid_2 with "Hbad Htok") as %Hbad.
      exfalso.
      naive_solver.
    }
    iSplitL "Hv".
    {
      rewrite /named; iExactEq "Hv"; do 3 f_equal.
      rewrite size_difference ?size_singleton; last by set_solver.
      eapply u64_set_size_all_lt in Hremaining.
      cut (size remaining ≠ 0%nat).
      { intros. word. }
      intros Heq0.
      apply size_empty_inv in Heq0. set_solver.
    }
    iSplitL "Htoks Htok".
    {
      iApply "Htoks".
      {
        iModIntro.
        iIntros (???) "[%Hremain|$]".
        iLeft.
        iPureIntro.
        set_solver.
      }
      {
        iFrame.
      }
    }
    iDestruct "HP" as "[$|HP]".
    iRight.
    iDestruct (big_sepS_elem_of_acc_impl n with "HP") as "[_ HP]".
    { set_solver. }
    iApply "HP".
    2:{ iFrame. }
    iModIntro.
    iIntros (???) "[$|[%Hremain|$]]".
    iRight. iLeft.
    iPureIntro. set_solver.
  }
  iNext.
  iIntros.
  iApply "HΦ".
  done.
Qed.

Lemma wp_WaitGroup__Wait wg γ P n :
  {{{
      own_WaitGroup wg γ n P
  }}}
    waitgroup.Wait wg
  {{{
        RET #(); [∗ set] i ∈ (fin_to_set u64), ⌜ uint.nat n ≤ uint.nat i ⌝ ∨ (P i)
  }}}.
Proof.
  iIntros (Φ) "(Hdone&Htotal'&#Hwg) HΦ".
  iLöb as "IH".
  wp_rec. wp_pures.
  iDestruct "Hwg" as (??) "(%HwgPair & Hlk)".
  rewrite HwgPair.
  wp_pures.

  wp_apply (wp_Mutex__Lock with "Hlk").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  iDestruct "HP" as "[Hbad|HP]".
  { iCombine "Hdone Hbad" gives %H. exfalso. naive_solver. }
  wp_load.
  wp_pures.

  iDestruct (ghost_var_agree with "[$] [$]") as %Heq.

  destruct (decide (W64 (size remaining) = W64 0)) as [Hsize|].
  - (* done. *)
    wp_apply (wp_Mutex__Unlock with "[$Hlocked $Hlk Htotal Htoks Hv Hdone]").
    {
      iNext.
      iExists _, _. iFrame. eauto.
    }
    wp_pures.
    rewrite bool_decide_true //.
    2:{ do 2 f_equal. done. }
    wp_pures.
    subst.
    iModIntro. iApply "HΦ". iApply (big_sepS_impl with "[$]").
    iModIntro. iIntros (x Hin) "[%Hge|[%Hinx|HPx]]".
    { auto. }
    { exfalso.
      eapply u64_set_size_all_lt in Hremaining.
      assert (size remaining = 0%nat) as Hzero.
      { apply word.of_Z_inj_small in Hsize; try lia.
        word. }
      apply size_empty_inv in Hzero. set_solver.
    }
    eauto.
  -
    wp_apply (wp_Mutex__Unlock with "[$Hlocked $Hlk Htotal Htoks Hv HP]").
    {
      iNext.
      iExists _, _. iFrame. eauto.
    }
    wp_pures.
    rewrite bool_decide_false.
    2:{ intros H. apply n0. apply inv_litv in H.
        apply base_lit_inv in H. done. }
    wp_pures.
    wp_apply ("IH" with "[$] [$]"). eauto.
Qed.

End proof.
End goose_lang.
