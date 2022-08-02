From iris.proofmode Require Import tactics.
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


From Perennial.program_proof.fencing Require Import map.
Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context `{!ffi_interp ffi}.
Context {ext_tys: ext_types ext}.

Local Coercion Var' (s:string): expr := Var s.

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
  Context `{!heapGS Σ} (N : namespace).
  Context `{!mapG Σ u64 unit}.
  Context `{!ghost_varG Σ u64}.

  Record waitgroup_names :=
    mkwaitgroup_names {
      tok_gn:gname;
      total_gn:gname
    }.

  Implicit Type γ:waitgroup_names.

  Definition own_WaitGroup_token γ (i:u64) : iProp Σ := i ⤳[γ.(tok_gn)] ().

  Definition is_WaitGroup wg γ P : iProp Σ :=
    ∃ lk (vptr:loc),
      ⌜wg = (lk, #vptr)%V⌝ ∗
      is_lock N lk (
        ∃ (remaining:gset u64) (total:u64),
          "%Hremaining" ∷ ⌜(∀ r, r ∈ remaining → int.nat r < int.nat total)⌝ ∗
          "Htotal" ∷ ghost_var γ.(total_gn) (1/2) total ∗
          "Hv" ∷ vptr ↦[uint64T] #(size remaining) ∗
          "Htoks" ∷ ([∗ set] i ∈ (fin_to_set u64), ⌜i ∈ remaining⌝ ∨ own_WaitGroup_token γ i) ∗
          "HP" ∷ ([∗ set] i ∈ (fin_to_set u64), ⌜int.nat i ≥ int.nat total⌝ ∨ ⌜i ∈ remaining⌝ ∨ (□ (P i)))
      ).

  (* XXX: here, wg is a value. Maybe it should be a loc? *)
  Definition own_WaitGroup (wg:val) γ (n:u64) (P:u64 → iProp Σ) : iProp Σ :=
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
  wp_call.
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

Lemma free_WaitGroup_alloc wg P :
  own_free_WaitGroup wg ={↑N}=∗ (∃ γ, own_WaitGroup wg γ 0 P).
Proof.
  iIntros "Hwg".
  iDestruct "Hwg" as (??) "(%Hwg & His_lock & Hv)".
  iMod (ghost_map_alloc_fin ()) as (γtok) "Htokens".
  iMod (ghost_var_alloc (U64 0)) as (γtotal) "[Htotal Ht2]".
  iExists (mkwaitgroup_names γtok γtotal).
  iFrame.
  iExists _, _.
  iSplitL ""; first done.
  simpl.

  iMod (alloc_lock with "His_lock [-]") as "$"; last done.
  iNext.
  iExists ∅, (U64 0).
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
    iApply (big_sepS_impl with "Htriv").
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

Lemma wp_WaitGroup__Add wg γ n P :
int.nat (word.add n 1) > int.nat n →
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
  wp_call.
  iDestruct "Hwg" as "(Htotal1 & #His)".
  iDestruct "His" as (??) "(%HwgPair & Hlk)".
  rewrite HwgPair.
  wp_pures.
  wp_apply (acquire_spec with "Hlk").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  iDestruct (ghost_var_agree with "Htotal1 Htotal") as %->.
  iMod (ghost_var_update_2 (word.add total 1) with "Htotal1 Htotal") as "[Htotal1 Htotal]".
  { by apply Qp_half_half. }
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
  iApply (release_spec with "[$Hlocked $Hlk Htotal HP Htoks Hv]").
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
      replace ((word.add 1 (size remaining))) with (U64 (size (remaining ∪ {[total]}))); last first.
      {
        (* TODO: pure reasoning: remaining has size less than n, and n is smaller than UINT64_MAX *)
        admit.
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

    iApply (big_sepS_impl with "HP").
    iModIntro.
    iIntros (??) "[%H1|[%H2|H3]]".
    {
      assert (int.nat x = int.nat total ∨ int.nat x ≥ int.nat (word.add total 1)) as Hcases.
      { word. }
      destruct Hcases as [|].
      {
        replace (x) with (total) by word.
        iRight. iLeft.
        iPureIntro. set_solver.
      }
      {
        iLeft. done.
      }
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
Admitted.

Lemma wp_WaitGroup__Done wg γ P n :
  {{{
      is_WaitGroup wg γ P ∗ own_WaitGroup_token γ n ∗ □ P n
  }}}
    waitgroup.Done wg
  {{{
        RET #(); True
  }}}.
Proof.
  iIntros (Φ) "(#Hwg & Htok & #HPn) HΦ".
  wp_call.
  iDestruct "Hwg" as (??) "(%HwgPair & Hlk)".
  rewrite HwgPair.
  wp_pures.

  wp_apply (acquire_spec with "Hlk").
  iIntros "[Hlocked Hown]".
  wp_pures.
  iNamed "Hown".
  wp_load.
  wp_store.

  iApply (release_spec with "[$Hlocked $Hlk Htotal HP Htoks Hv Htok HPn]").
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
      (* Pure reasoning; need to know that (size remaining) is less than UINT64_MAX *)
      admit.
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
    iApply (big_sepS_impl with "HP").
    iModIntro.
    iIntros (??) "[$|[%Hremain|$]]".
    destruct (decide (x = n)) as [->|].
    {
      iFrame "HPn".
    }
    {
      iRight. iLeft.
      iPureIntro. set_solver.
    }
  }
  iNext.
  iIntros.
  iApply "HΦ".
  done.
Admitted.

Lemma wp_WaitGroup__Wait wg γ P n :
  {{{
      own_WaitGroup wg γ n P
  }}}
    waitgroup.Wait wg
  {{{
        RET #(); [∗ set] i ∈ (fin_to_set u64), ⌜int.nat i ≥ int.nat n⌝ ∨ (P n)
  }}}.
Proof.
Admitted.

End proof.
End goose_lang.
