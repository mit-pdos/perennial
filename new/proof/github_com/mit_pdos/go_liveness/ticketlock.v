Require Import New.generatedproof.github_com.mit_pdos.go_liveness.ticketlock.
Require Import New.proof.sync.atomic.
Require Import New.proof.runtime.
Require Import New.proof.proof_prelude.
From New.proof Require Import grove_prelude.
From iris.base_logic.lib Require Import ghost_map.

Set Implicit Arguments.

Section proof.

Context `{!heapGS Σ}.
Context `{!ghost_mapG Σ w64 bool}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : ticketlock.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) ticketlock := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) ticketlock := build_get_is_pkg_init_wf.
Definition own_ticketlock_inner (ptr: loc) (cur: w64) (next: w64) : iProp Σ :=
  "Hcur" ∷ own_Uint64 (struct.field_ref_f ticketlock.TicketLock "cur" ptr) (DfracOwn 1) cur ∗
  "Hnext" ∷ own_Uint64 (struct.field_ref_f ticketlock.TicketLock "next" ptr) (DfracOwn 1) next.

Definition own_ticketlock (ptr: loc) (g_held: gname) (P: iProp Σ) : iProp Σ :=
  ∃ (cur: w64) (next: w64) (held: gmap w64 bool),
    "Hinner" ∷ own_ticketlock_inner ptr cur next ∗
    "Hheld" ∷ ghost_map_auth g_held 1 held ∗
    "HP" ∷ (match held !! cur with
            | None => P
            | Some false => P
            | Some true => True
            end) ∗
    "Hheldbound" ∷ ⌜ ∀ (n: w64), uint.nat n >= uint.nat next -> held !! n = None ⌝ ∗
    "Hcurbound" ∷ ⌜ uint.nat cur < uint.nat next ∨
                    ( cur = next ∧ held !! cur = None ) ⌝.
    (* Could also enforce that held values below cur are not in the map.
       This would be important for proving correctness when tickets wrap around,
       as long as next never catches up to cur from the wrong side. *)

Definition is_ticketlock (ptr: loc) (g: gname) (P: iProp Σ) : iProp Σ :=
  inv nroot (own_ticketlock ptr g P).

Definition holding_ticketlock (g: gname) : iProp Σ :=
  ∃ n,
    n ↪[g] true.

Lemma wp_TicketLock_New :
  {{{
        is_pkg_init ticketlock ∗
        True
  }}}
    @! ticketlock.New #()
  {{{
        (ptr: loc), RET #ptr; own_ticketlock_inner ptr 0 0
  }}}.
Proof.
  wp_start as "HP".
  wp_auto.
  iApply "HΦ".
  iDestruct (struct_fields_split with "t") as "t". iNamed "t".
  iFrame.
Qed.

Lemma init_TicketLock E ptr (P: iProp Σ) :
  own_ticketlock_inner ptr 0 0 ∗ P
    ={E}=∗
  ∃ g, is_ticketlock ptr g P.
Proof.
  iIntros "[Hinner HP]".
  iMod (ghost_map_alloc (∅: gmap w64 bool)) as (g_held) "[Hheld _]".
  iMod (inv_alloc nroot _ (own_ticketlock ptr g_held P) with "[Hheld Hinner HP]") as "$".
  {
    iNext. iFrame. iSplitL.
    { destruct (∅ !! (W64 0%nat)); last done. destruct b; done. }
    iPureIntro. auto.
  }
  done.
Qed.

Lemma wp_TicketLock__Acquire (ptr : loc) g P :
  {{{
        is_pkg_init ticketlock ∗
        is_ticketlock ptr g P
  }}}
    ptr @ (ptrT.id ticketlock.TicketLock.id) @ "Acquire" #()
  {{{
        RET #(); P ∗ holding_ticketlock g
  }}}.
Proof.
  wp_start as "#Htl".
  wp_auto.
  wp_apply (wp_Uint64__Add).

  iInv "Htl" as "Hi" "Hclose".
  iDestruct "Hi" as (cur next held) "(>Hinner & >Hheld & HP & >%Hheldbound & >%Hcurbound)".
  iNamed "Hinner". iNamed "Hinner".

  iMod (ghost_map_insert next false with "Hheld") as "[Hheld Hnextheld]".
  { apply Hheldbound. word. }

  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iFrame.
  iIntros "!> Hnext".
  iMod "Hmask".
  iMod ("Hclose" with "[Hcur Hnext Hheld HP]").
  {
    iNext. iFrame "Hcur Hnext Hheld".
    iSplitL.
    {
      rewrite lookup_insert. destruct (decide (next = cur)).
      - rewrite Hheldbound; first done. word.
      - done.
    }
    iSplitL.
    {
      iPureIntro.
      intros.
      rewrite lookup_insert. destruct (decide (next = n)).
      - (* assuming no overflow, this would have been true. *)
        admit.
      - rewrite Hheldbound; eauto.
        (* assuming no overflow, this would have been true. *)
        admit.
    }
    iPureIntro.
    (* assuming no overflow, this would have been true. *)
    admit.
  }

  iModIntro.
  wp_auto.
  wp_apply (wp_for with "[t my Hnextheld HΦ]").
  { iNamedAccu. }
  iModIntro. iNamed 1.
  wp_auto.

  wp_apply (wp_Uint64__Load).

  iInv "Htl" as "Hi" "Hclose".
  iDestruct "Hi" as (cur' next' held') "(>Hinner & >Hheld & HP & >%Hheldbound' & >%Hcurbound')".
  iNamed "Hinner". iNamed "Hinner".

  destruct (decide (cur' = next)).
  - iDestruct (ghost_map_lookup with "Hheld Hnextheld") as "%Hnextsome".
    iMod (ghost_map_update true with "Hheld Hnextheld") as "[Hheld Hnextheld]".

    iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iFrame.
    iIntros "!> Hcur".
    iMod "Hmask".
    iMod ("Hclose" with "[Hcur Hnext Hheld]").
    {
      iNext. iFrame "Hcur Hnext Hheld".
      iSplitL.
      { subst.
        rewrite lookup_insert_eq. done. }
      iSplitL.
      {
        iPureIntro.
        intros.
        rewrite lookup_insert. destruct (decide (next = n)).
        - rewrite Hheldbound' in Hnextsome; first done. word.
        - rewrite Hheldbound'; eauto.
      }
      iPureIntro.
      subst.
      rewrite lookup_insert_eq. left.
      destruct Hcurbound' as [Hcurbound'|Hcurbound']; eauto.
      rewrite Hnextsome in Hcurbound'. intuition congruence.
    }

    iModIntro.
    wp_auto.
    wp_if_destruct.
    { iApply "HΦ".
      rewrite Hnextsome. iFrame.
    }
    word.

  - iApply fupd_mask_intro.
    { solve_ndisj. }
    iIntros "Hmask".
    iFrame.
    iIntros "!> Hcur".
    iMod "Hmask".
    iMod ("Hclose" with "[Hcur Hnext Hheld HP]").
    {
      iNext. iFrame "Hcur Hnext Hheld HP". done.
    }

    iModIntro.
    wp_auto.
    wp_if_destruct.
    { exfalso. word. }
    wp_apply (wp_Gosched with "[]").
    { done. }

    wp_for_post.
    iFrame.
    Fail idtac.
Admitted.

Lemma wp_TicketLock__Release (ptr : loc) g P :
  {{{
        is_pkg_init ticketlock ∗
        is_ticketlock ptr g P ∗
        holding_ticketlock g ∗
        P
  }}}
    ptr @ (ptrT.id ticketlock.TicketLock.id) @ "Release" #()
  {{{
        RET #(); True
  }}}.
Proof.
  wp_start as "(#Htl & Hholding & HP)".
  wp_auto.
  wp_apply wp_Uint64__Add.

  iInv "Htl" as "Hi" "Hclose".
  iDestruct "Hi" as (cur next held) "(>Hinner & >Hheld & Hip & >%Hheldbound & >%Hcurbound)".
  iNamed "Hinner". iNamed "Hinner".

  iDestruct "Hholding" as (n) "Hnextheld".
  iDestruct (ghost_map_lookup with "Hheld Hnextheld") as "%Hnextsome".
  (* XXX could ghost_map_delete to allow ticket wraparound *)

  (* XXX need to strengthen invariant:
    there must be at most one held=true value, and if it's present, it must be cur.
    to support this, need to delete released tickets.
  *)

  iApply fupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hmask".
  iFrame.
  iIntros "!> Hcur".
  iMod "Hmask".
  iMod ("Hclose" with "[Hcur Hnext Hheld HP]").
  {
    iNext. iFrame "Hcur Hnext Hheld".
    iSplitL.
    {
      destruct (held !! w64_word_instance.(word.add) cur (W64 1)) eqn:He; rewrite He.
      { destruct b; done. }
      done.
    }
    iSplitL.
    { done. }
    iPureIntro.
    destruct (decide (uint.nat (word.add cur (W64 1)) = uint.nat next)).
    (* assuming no overflow, this would have been true. *)
    { admit. }
    admit.
  }

  iModIntro.
  wp_auto.
  by iApply "HΦ".
  Fail idtac.
Admitted.

End proof.
