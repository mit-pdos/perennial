Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.

(** * Done Channel Pattern Verification

    This file provides the "done channel" idiom spec - a
    signaling mechanism where one sender closes the channel to notify one or more
    receivers, with each receiver obtaining their designated resources.

    If the resources you are transferring are persistent, you can use the Broadcast versions of each lemma that are persistent 

    Key features:
    - Single closer with exclusive Notify token
    - Multiple receivers with Notified tokens (exclusive resources)
    - Multiple receivers with BroadcastNotified tokens (duplicable resources)
    - Each receiver gets their specific resource upon channel close
*)

Section done.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Set Default Proof Using "All".

Record done_names := {
  chan_name : chan_names;
  receivers_map_name : gname;
  broadcast_map_name : gname;
  acc_name         : gname
}.

Definition NotifyInternal (γ : done_names) (Qs : list (iProp Σ)) (duplicableQs : list (iProp Σ)) : iProp Σ :=
  ∃ (m : gmap nat gname) (m_bc : gmap nat gname),
    ghost_map_auth γ.(receivers_map_name) (1/2) m ∗
    ghost_map_auth γ.(broadcast_map_name) (1/2) m_bc ∗
    ⌜∀ i, i ≥ length Qs → m !! i = None⌝ ∗
    ⌜∀ i, i ≥ length duplicableQs → m_bc !! i = None⌝ ∗
    ([∗ list] i ↦ Q ∈ Qs,
      ∃ prop_gname,
        i ↪[γ.(receivers_map_name)]{#1/2} prop_gname ∗
        saved_prop_own prop_gname (DfracOwn(1/2)) Q) ∗
    ([∗ list] i ↦ Q ∈ duplicableQs,
      ∃ prop_gname,
        i ↪[γ.(broadcast_map_name)]{DfracDiscarded} prop_gname ∗
        saved_prop_own prop_gname DfracDiscarded Q).

Definition Notify (γ : done_names) (R : iProp Σ) : iProp Σ :=
  ∃ Qs duplicableQs, NotifyInternal γ Qs duplicableQs ∗ saved_prop_own γ.(acc_name) (DfracOwn 1) R
∗ (R -∗ ([∗ list] Q ∈ Qs, Q) ∗ ([∗ list] Q ∈ duplicableQs, Q)) .

Definition Notified (γ : done_names) (Q : iProp Σ) : iProp Σ :=
  ∃ prop_gname (i : nat),
    i ↪[γ.(receivers_map_name)]{#1/2} prop_gname ∗
    saved_prop_own prop_gname (DfracOwn (1/2)) Q.

Definition BroadcastNotified (γ : done_names) (Q : iProp Σ) : iProp Σ :=
  ∃ prop_gname (i: nat),
    i ↪[γ.(broadcast_map_name)]{DfracDiscarded} prop_gname ∗
    saved_prop_own prop_gname DfracDiscarded Q.

Global Instance BroadcastNotified_persistent γ Q : Persistent (BroadcastNotified γ Q).
Proof.
  rewrite /BroadcastNotified.
  apply _.
Qed.

Definition is_done (γ : done_names) (ch : loc) : iProp Σ :=
  is_chan ch γ.(chan_name) V ∗
  inv nroot (
    ∃ s (m : gmap nat gname) (m_bc : gmap nat gname) (Qs: list (iProp Σ)) (duplicableQs : list (iProp Σ)),
      "Hch" ∷ own_chan γ.(chan_name) V s  ∗
      "Hmap" ∷ ghost_map_auth γ.(receivers_map_name) (1/2)%Qp m ∗
      "Hmap_bc" ∷ ghost_map_auth γ.(broadcast_map_name) (1/2)%Qp m_bc ∗
      match s with
      | chanstate.Idle => True
      | chanstate.RcvPending => True
      | chanstate.Closed [] =>
          "%Hbound" ∷ ⌜∀ i, i ≥ length Qs → m !! i = None⌝ ∗
          "%Hbound_bc" ∷ ⌜∀ i, i ≥ length duplicableQs → m_bc !! i = None⌝ ∗
          "Hgm" ∷ ghost_map_auth γ.(receivers_map_name) (1/2)%Qp m ∗
          "Hgm_bc" ∷ ghost_map_auth γ.(broadcast_map_name) (1/2)%Qp m_bc ∗
          "Hrecv" ∷
            ([∗ list] i ↦ Q ∈ Qs,
              ∃ prop_gname,
                i ↪[γ.(receivers_map_name)]{#1/2} prop_gname ∗
                (((saved_prop_own prop_gname (DfracOwn (1/2)) Q) ∗ Q) ∨
                 ((saved_prop_own prop_gname (DfracOwn (1)) Q)))) ∗
          "Hrecv_bc" ∷
            ([∗ list] i ↦ Q ∈ duplicableQs,
              ∃ prop_gname,
                i ↪[γ.(broadcast_map_name)]{DfracDiscarded} prop_gname ∗
                saved_prop_own prop_gname DfracDiscarded Q ∗
                Q)
      | _ => False
      end
  )%I.

Lemma done_alloc_notified γ ch R Q :
  is_done γ ch -∗
  Notify γ R ={⊤}=∗
  Notify γ (R ∗ Q) ∗
  Notified γ Q.
Proof.
  iIntros "#Hdone HNotifyInternal".
  rewrite /Notify /Notified /is_done.
  iDestruct "HNotifyInternal" as (Qs duplicableQs) "(HQs & Hsp & HRQs)".
  iDestruct "Hdone" as "[#Hch #Hinv]".
  iMod (saved_prop_alloc Q (DfracOwn 1)) as (prop_gname) "Hprop"; first done.
  iDestruct "Hprop" as "[Hprop1 Hprop2]".
  set (i := length Qs).
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  unfold NotifyInternal.
  iNamed "HQs".
  iDestruct "HQs" as "(Hauth_half & Hauth_bc_half & %H & %H_bc & HQs & HQs_bc)".
  iDestruct "Hinv_open" as (s m' m_bc' Qs' duplicableQs') "(>Hch_own & >Hmap_half & >Hmap_bc_half & Hstate)".
  iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m m') with "[$Hauth_half] [$Hmap_half]") as %->.
  iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m_bc m_bc') with "[$Hauth_bc_half] [$Hmap_bc_half]") as %->.
  iCombine "Hauth_half Hmap_half" as "Hauth_full".
  iMod (ghost_map_insert i prop_gname with "Hauth_full") as "[Hauth_full Hfrag]".
  {
    specialize H with i.
    assert (i ≥ i) by lia. apply H in H0. done.
  }
  iDestruct "Hauth_full" as "[Hauth_half1 Hauth_half2]".
  iDestruct "Hfrag" as "[Hfrag1 Hfrag2]".
  iAssert (
  [∗ list] i0↦Q0 ∈ (Qs ++ [Q]),
    ∃ pg, i0 ↪[γ.(receivers_map_name)]{#1/2} pg ∗
           saved_prop_own pg (DfracOwn (1/2)) Q0
)%I
with "[HQs Hfrag1 Hprop1]" as "HQs_ext".
{
  iApply (big_sepL_app with "[$HQs Hfrag1 Hprop1]").
  rewrite big_sepL_singleton.
  iFrame.
  replace (length Qs + 0)%nat with (length Qs) by done.
  done.
}
iMod (saved_prop_update (R ∗ Q) with "Hsp") as "Hsp".
  destruct s; try iDestruct "Hstate" as ">Hstate"; try done.
  {
    iMod ("Hinv_close" with "[Hch_own Hauth_half2 Hmap_bc_half Hstate]").
    {
      iNext. iExists chanstate.Idle. iExists (<[i := prop_gname]> m'). iExists m_bc'. iFrame. iExists []. iExists [].
      done.
    }
    {
      iModIntro. iFrame. subst i. iSplitL "".
      {
        iPureIntro. split. 
        { intros j Hj.
        rewrite length_app /= in Hj.
        destruct (decide (j = length Qs)) as [->|Hne].
        - lia.
        - rewrite lookup_insert_ne; last done.
          apply H. lia.
        }
        {
         intros i Hi. set_solver.
        }
      }
      iIntros "[HR' HQ]".
      iDestruct ("HRQs" with "HR'") as "[HQs' HQs_bc']".
      iFrame.
    }
  }
  {
    iMod ("Hinv_close" with "[Hch_own Hauth_half2 Hmap_bc_half Hstate]").
    {
      iNext. iFrame.
      iExists []. iExists []. done.
    }
    {
      iModIntro. iFrame.
      replace (length Qs + 0)%nat with (length Qs) by lia.
      iFrame.
      iSplitL "". { iPureIntro.
 intros.
      subst i.
      split. { 
        rewrite length_app. intros i Hi.
        rewrite lookup_insert_ne.
          - apply H. lia.
          - simpl in Hi. destruct i. { lia. } { lia. }
      }
      {
       intros i Hi. set_solver. 
      } 
      }
       iIntros "[HR' HQ]".
      iDestruct ("HRQs" with "HR'") as "[HQs' HQs_bc']".
      iFrame.
    }
  }
  {
    destruct drain.
    - iDestruct "Hstate" as "[>%Hc Hgm]".
      iDestruct "Hgm" as "(>? & >? & ?)". iNamed.
      iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m' (<[i:=prop_gname]> m')) with "[$Hgm] [$Hauth_half1]") as %->.
      iCombine "Hauth_half2 Hauth_half1" as "Hgm2".
      iDestruct ((ghost_map_auth_agree) with "[$Hgm] [$Hgm2]") as %->.
      iDestruct (ghost_map_auth_valid with "Hgm2") as %Hvalid1.
      iDestruct (ghost_map_auth_valid_2 with "Hgm2 Hgm") as %[Hvalid2 _].
      done.
    - iDestruct "Hstate" as ">Hstate". done.
  }
Qed.

Lemma done_alloc_broadcast_notified γ ch R Q `{!Persistent Q} :
  is_done γ ch -∗
  Notify γ R ={⊤}=∗
  Notify γ (R ∗ Q) ∗
  BroadcastNotified γ Q.
Proof.
  iIntros "#Hdone HNotifyInternal".
  rewrite /Notify /BroadcastNotified /is_done.
  iDestruct "HNotifyInternal" as (Qs duplicableQs) "(HQs & Hsp & HRQs)".
  iDestruct "Hdone" as "[#Hch #Hinv]".
  iMod (saved_prop_alloc Q DfracDiscarded) as (prop_gname) "Hprop"; first done.
  set (i := length duplicableQs).
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  unfold NotifyInternal.
  iNamed "HQs".
  iDestruct "HQs" as "(Hauth_half & Hauth_bc_half & %H & %H_bc & HQs & HQs_bc)".
  iDestruct "Hinv_open" as (s m' m_bc' Qs' duplicableQs') "(>Hch_own & >Hmap_half & >Hmap_bc_half & Hstate)".
  iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m m') with "[$Hauth_half] [$Hmap_half]") as %->.
  iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m_bc m_bc') with "[$Hauth_bc_half] [$Hmap_bc_half]") as %->.
  iCombine "Hauth_bc_half Hmap_bc_half" as "Hauth_bc_full".
  iMod (ghost_map_insert_persist i prop_gname with "Hauth_bc_full") as "[Hauth_bc_full Hfrag]".
  {
    specialize H_bc with i.
    assert (i ≥ i) by lia. apply H_bc in H0. done.
  }
  iDestruct "Hauth_bc_full" as "[Hauth_bc_half1 Hauth_bc_half2]".
  iAssert (
  [∗ list] i0↦Q0 ∈ (duplicableQs ++ [Q]),
    ∃ pg, i0 ↪[γ.(broadcast_map_name)]{DfracDiscarded} pg ∗
           saved_prop_own pg DfracDiscarded Q0
)%I
with "[HQs_bc Hfrag Hprop]" as "HQs_bc_ext".
{
  iApply (big_sepL_app with "[$HQs_bc Hfrag Hprop]").
  rewrite big_sepL_singleton.
  iFrame.
  replace (length duplicableQs + 0)%nat with (length duplicableQs) by done.
  iFrame.
}
iDestruct "HQs_bc_ext" as "#HQs_bc_ext". 
iDestruct (big_sepL_lookup_acc _ _ (length duplicableQs) Q with "HQs_bc_ext") as "[#H0 H1]".
{ rewrite lookup_app_r. { 
  replace (length duplicableQs - length duplicableQs) with 0 by lia.
  simpl. 
  rewrite Nat.sub_diag. done.
}
{
 done. 
}
}
iMod (saved_prop_update (R ∗ Q) with "Hsp") as "Hsp".
  destruct s; try iDestruct "Hstate" as ">Hstate"; try done.
  {
    iMod ("Hinv_close" with "[Hch_own Hauth_half Hauth_bc_half2 Hstate]").
    {
      iNext. iExists chanstate.Idle. iExists m'. iExists (<[i := prop_gname]> m_bc'). iFrame. iExists []. iExists [].
      done.
    }
    {
      iModIntro. 
      iFrame. subst i. 
      iFrame. iFrame "%#".
      iSplitL "HRQs". { iSplitL "". { iPureIntro. intros i Hi.
      rewrite lookup_insert_ne.
- apply H_bc. rewrite length_app in Hi. simpl in Hi. lia.
- rewrite length_app in Hi. simpl in Hi. lia.
      }
      iIntros "[HR HQ]".
      iApply "HRQs" in "HR".
      iDestruct "HR" as "[HQs HdQs]".
      iFrame.
        done. 
      }
      set (i := length duplicableQs).
      iAssert ([∗ list] k↦y ∈ (duplicableQs ++ [Q]), ∃ pg : gname,
k ↪[γ .(broadcast_map_name)]□ pg ∗
saved_prop_own pg DfracDiscarded y)%I with "[H1 H0]" as "#H".
{
 iApply "H1". iFrame "#". 
}
iNamed "H0".
 iDestruct "H0" as "[#HdQ #Hspo]".
replace (length duplicableQs + 0)%nat with (length duplicableQs) by lia.
simpl. 
      iFrame "#".
    }
  }
  {
    iMod ("Hinv_close" with "[Hch_own Hauth_half Hauth_bc_half2 Hstate]").
    {
      iNext. iFrame.
      iExists []. iExists []. done.
    }
    {
      iModIntro. 
      iFrame. subst i. 
      iFrame. iFrame "%#".
      iSplitL "HRQs". { iSplitL "". { iPureIntro. intros i Hi.
      rewrite lookup_insert_ne.
- apply H_bc. rewrite length_app in Hi. simpl in Hi. lia.
- rewrite length_app in Hi. simpl in Hi. lia.
      }
      iIntros "[HR HQ]".
      iApply "HRQs" in "HR".
      iDestruct "HR" as "[HQs HdQs]".
      iFrame.
        done. 
      }
      set (i := length duplicableQs).
      iAssert ([∗ list] k↦y ∈ (duplicableQs ++ [Q]), ∃ pg : gname,
k ↪[γ .(broadcast_map_name)]□ pg ∗
saved_prop_own pg DfracDiscarded y)%I with "[H1 H0]" as "#H".
{
 iApply "H1". iFrame "#". 
}
iNamed "H0".
 iDestruct "H0" as "[#HdQ #Hspo]".
replace (length duplicableQs + 0)%nat with (length duplicableQs) by lia.
simpl. 
      iFrame "#".
    }
  }
   
  {
    destruct drain.
    - iDestruct "Hstate" as "[>%Hc Hgm]".
      iDestruct "Hgm" as "(>? & >? & >? & ?)". iNamed.
      iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m_bc' (<[i:=prop_gname]> m_bc')) with "[$Hgm_bc] [$Hauth_bc_half1]") as %->.
      iCombine "Hauth_bc_half2 Hauth_bc_half1" as "Hgm_bc2".
      iDestruct ((ghost_map_auth_agree) with "[$Hgm_bc] [$Hgm_bc2]") as %->.
      iDestruct (ghost_map_auth_valid with "Hgm_bc2") as %Hvalid1.
      iDestruct (ghost_map_auth_valid_2 with "Hgm_bc2 Hgm_bc") as %[Hvalid2 _].
      done.
    - iDestruct "Hstate" as ">Hstate". done.
  }
Qed.

Lemma start_done (ch : loc) (γ : chan_names) :
  is_chan ch γ V -∗
  own_chan γ V chanstate.Idle ={⊤}=∗
  ∃ γdone, is_done γdone ch ∗ Notify γdone True.
Proof.
  iIntros "#Hch Hoc".
  iMod (ghost_map_alloc_empty (K:=nat) (V:=gname)) as (γmap) "[Hmap_auth1 Hmap_auth2]".
  iMod (ghost_map_alloc_empty (K:=nat) (V:=gname)) as (γmap_bc) "[Hmap_bc_auth1 Hmap_bc_auth2]".
  iMod (saved_prop_alloc (emp : iProp Σ) (DfracOwn 1)) as (γacc) "Hacc_full".
  {
    done.
  }
  set (γdone := {|
    chan_name := γ;
    receivers_map_name := γmap;
    broadcast_map_name := γmap_bc;
    acc_name := γacc

  |}).
  iMod (inv_alloc nroot _ (
    ∃ s m m_bc Qs duplicableQs,
      "Hch" ∷ own_chan γ V s ∗
      "Hmap" ∷ ghost_map_auth γmap (1/2)%Qp m ∗
      "Hmap_bc" ∷ ghost_map_auth γmap_bc (1/2)%Qp m_bc ∗
      match s with
      | chanstate.Idle => True
      | chanstate.RcvPending => True
      | chanstate.Closed [] =>
          "%Hbound" ∷ ⌜∀ i, i ≥ length Qs → m !! i = None⌝ ∗
          "%Hbound_bc" ∷ ⌜∀ i, i ≥ length duplicableQs → m_bc !! i = None⌝ ∗
          "Hgm" ∷ ghost_map_auth γmap (1/2)%Qp m ∗
          "Hgm_bc" ∷ ghost_map_auth γmap_bc (1/2)%Qp m_bc ∗
          "Hrecv" ∷
            ([∗ list] i ↦ Q ∈ Qs,
              ∃ prop_gname,
                i ↪[γmap]{#1/2} prop_gname ∗
                (((saved_prop_own prop_gname (DfracOwn (1/2)) Q) ∗ Q) ∨
                 ((saved_prop_own prop_gname (DfracOwn (1)) Q)))) ∗
          "Hrecv_bc" ∷
            ([∗ list] i ↦ Q ∈ duplicableQs,
              ∃ prop_gname,
                i ↪[γmap_bc]{DfracDiscarded} prop_gname ∗
                saved_prop_own prop_gname DfracDiscarded Q ∗
                Q)
      | _ => False
      end
  )%I with "[Hoc Hmap_auth1 Hmap_bc_auth1]") as "#Hinv".
  {
    iNext. iExists chanstate.Idle, ∅, ∅.
    iFrame. iExists [], []. done.
  }
  iModIntro. iExists γdone. iFrame "#".
  rewrite /NotifyInternal. replace (γdone.(chan_name)) with γ by done. iFrame.
  replace (γdone.(receivers_map_name)) with γmap by done.
  replace (γdone.(broadcast_map_name)) with γmap_bc by done.
  iFrame.
  iDestruct (big_sepL_nil (λ i Q, ∃ prop_gname : gname, i ↪[γmap]{#1 / 2} prop_gname ∗ saved_prop_own prop_gname (DfracOwn (1 / 2)) Q)%I) as "H".
  iDestruct (big_sepL_nil (λ i Q, ∃ prop_gname : gname, i ↪[γmap_bc]{DfracDiscarded} prop_gname ∗ saved_prop_own prop_gname DfracDiscarded Q)%I) as "H_bc".
  iExists [], [].
  iSplitR "".
  {
  iFrame.
  iSplitL "". { iFrame. iPureIntro. done. }
  iSplitL "". { iPureIntro. done. }
  simpl.
  iFrame.
  done.
  }
  {
    simpl. iIntros "_". iFrame.
    done.
  }
Qed.

Lemma start_done_with_notified (ch : loc) (γ : chan_names) (Q : iProp Σ) :
  is_chan ch γ V -∗
  own_chan γ V chanstate.Idle ={⊤}=∗
  ∃ γdone, is_done γdone ch ∗ Notify γdone Q ∗ Notified γdone Q.
Proof.
  iIntros "#Hch Hoc".
  iMod (start_done with "Hch Hoc") as (γdone) "[#Hdone HNotify]".
  iMod (done_alloc_notified with "Hdone HNotify") as "[HNotify HNotified]".
  iDestruct "HNotify" as (Qs duplicableQs) "(HInternal & Hsp & HRQs)".
  iMod (saved_prop_update Q with "Hsp") as "Hsp".
  iModIntro.
  iExists γdone. 
  iFrame "∗#".
  iIntros "HQ".
  iApply "HRQs".
  iFrame.
Qed.

Lemma start_done_with_broadcast_notified (ch : loc) (γ : chan_names) (Q : iProp Σ) `{!Persistent Q} :
  is_chan ch γ V -∗
  own_chan γ V chanstate.Idle ={⊤}=∗
  ∃ γdone, is_done γdone ch ∗ Notify γdone Q ∗ BroadcastNotified γdone Q.
Proof.
  iIntros "#Hch Hoc".
  iMod (start_done with "Hch Hoc") as (γdone) "[#Hdone HNotify]".
  iMod (done_alloc_broadcast_notified with "Hdone HNotify") as "[HNotify HBroadcastNotified]".
  {
    done.
  }
  iDestruct "HNotify" as (Qs duplicableQs) "(HInternal & Hsp & HRQs)".
  iMod (saved_prop_update Q with "Hsp") as "Hsp".
  iModIntro.
  iExists γdone. 
  iFrame "∗#".
  iIntros "HQ".
  iApply "HRQs".
  iFrame.
Qed.

Lemma done_is_chan γ ch :
  is_done γ ch ⊢ is_chan ch γ.(chan_name) V.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma done_close_au γ ch R Φ :
  is_done γ ch -∗
  £1 ∗ £1 ∗ £1 -∗
  Notify γ R ∗ R -∗
  ▷ Φ -∗
  close_au γ.(chan_name) V Φ.
Proof.
  iIntros "#Hdone". iIntros "(Hlc1 & Hlc2 & Hlc3)". iIntros "[HNh HR]".
  unfold Notify. iNamed "HNh". iDestruct "HNh" as "[HProps Hsp]".
  unfold NotifyInternal.
  iNamed "HProps".
  iDestruct "HProps" as "(Hgm & Hgm_bc & %Hlen & %Hlen_bc & HQs & HQs_bc)".
  unfold is_done. iDestruct "Hdone" as "[Hch Hinv]". iIntros "Hcont".
  iMod (lc_fupd_elim_later with "[$] Hcont") as "Hcont".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hinv_open" as (s m' m_bc' Qs' duplicableQs') "(Hch_own & Hmap_half & Hmap_bc_half & Hstate)".
  iDestruct (ghost_map_auth_agree with "Hgm Hmap_half") as %->.
  iDestruct (ghost_map_auth_agree with "Hgm_bc Hmap_bc_half") as %->.
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.
  destruct s; try done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod (lc_fupd_elim_later with "[$] Hinv_close") as "Hinv_close".
    iDestruct "Hsp" as "[Hsp Hrs]".
    iDestruct ("Hrs" with "HR") as "[HR HR_bc]".
    iMod ("Hinv_close" with "[Hmap_half Hmap_bc_half Hsp Hoc HR HR_bc Hgm Hgm_bc HQs HQs_bc]") as "_".
    {
      iNext. iExists (chanstate.Closed []), m', m_bc'. iFrame "Hmap_half Hmap_bc_half".
      iFrame. iExists Qs, duplicableQs.
      iSplitL "". { iPureIntro. done. }
      iSplitL "". { iPureIntro. done. }
      iFrame.
      iSplitL "HR HQs".
      {
      iDestruct ((big_sepL_sep_2) with "[$HR] [$HQs]") as "H".
      iApply (big_sepL_mono with "H").
      {
        iIntros (k). iIntros (y). iIntros "%H". iIntros "H". iDestruct "H" as "[H y]".
        iFrame. iNamed "H". iNamed "y". iExists prop_gname. iDestruct "y" as "[H1 H2]".
        iFrame. iLeft. iFrame.
      }
      }
      {
        iDestruct ((big_sepL_sep_2) with "[$HR_bc] [$HQs_bc]") as "H".
        iApply (big_sepL_mono with "H").
        iIntros (k y ?). iIntros "[HQ Hbc]".
        iNamed "Hbc". iDestruct "Hbc" as "[Hbc1 Hbc2]".
         iExists prop_gname. iFrame.
      }
    }
    iModIntro. iApply "Hcont".
  - destruct drain; try done.
    iNamed "Hstate".
    iCombine "Hmap_half Hgm" as "H". iNamed "Hstate".
    iCombine "Hgm_bc Hmap_bc_half" as "Hgm_bc_combined".
iNamed "Hstate".
iDestruct (ghost_map_auth_valid with "Hgm_bc_combined") as %Hvalid1.
iDestruct (ghost_map_auth_valid_2 with "Hgm_bc_combined Hgm_bc") as %[Hvalid2 _].
done.
Qed.

Lemma wp_done_close γ ch R `[ct ↓u go.ChannelType dir t]:
  {{{ is_done γ ch ∗
      Notify γ R ∗ R }}}
    #(functions go.close [ct]) #ch
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ). iIntros "(#Hdone & Hrest)".  iNamed "Hrest".
  iDestruct "Hrest" as "[HNh HR]".
  iIntros "Hphi".
  unfold is_done. iDestruct "Hdone" as "[Hch Hinv]".
  iApply (chan.wp_close with "Hch").
  iIntros "Hlc". iDestruct "Hlc" as "[Hlc Hlcrest]".
  iApply (done_close_au with "[][$][$HNh $HR][Hphi]").
  { iFrame "#". }
  iNext. iApply "Hphi". done.
Qed.

Lemma done_receive_au γ ch Q  :
  ∀ (Φ: V → bool → iProp Σ),
  is_done γ ch -∗
  Notified γ Q -∗
  ▷ (Q -∗ Φ (zero_val V) false) -∗
  £1 ∗ £1 ∗ £1 ∗ £1 -∗
  recv_au γ.(chan_name) V (λ (v:V) (ok:bool), Φ v ok).
Proof.
  intros Φ.
  iIntros "#Hdone".
  iIntros "HNotified".
  iIntros "HphiQ".
  iIntros "(? & ? & ? & ?)".
   unfold is_done. iDestruct "Hdone" as "[Hch Hinv]".
  unfold NotifyInternal.


  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch0".
  iNamed "Hinv_open".
  destruct s; try done.
  {
    iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iFrame.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc Hmap Hmap_bc]") as "_".
    {
      iNext. iFrame. iExists [], []. done.
    }
    iModIntro.
    unfold recv_nested_au.
    iInv "Hinv" as "Hinv_open1" "Hinv_close".
    iMod (lc_fupd_elim_later with "[$] Hinv_open1") as "Hinv_open1".
    iNamed "Hinv_open1".
    destruct s; try done.
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
      destruct drain.
      {
        iIntros "Hoc".
        iMod "Hmask". iNamed "Hinv_open1". iNamed "HNotified".
        iDestruct "HNotified" as "[Hn1 Hn2]".
        iDestruct (ghost_map_lookup with "Hmap Hn1") as %Hlookup.
        have Hi_lt : i < length Qs0.
        {
          destruct (decide (i < length Qs0)) as [H|Hge]; [exact H|].
          have Hge' : i ≥ length Qs0 by lia.
          rewrite (Hbound i Hge') in Hlookup. discriminate.
        }
        destruct (lookup_lt_is_Some_2 Qs0 i ltac:(lia)) as [x Hx].
        iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv") as "[H H2]".
        iNamed "H". iDestruct "H" as "[H3 H4]".
        iDestruct (ghost_map_elem_agree with "Hn1 H3") as %Heq.
        subst prop_gname0.
        iDestruct "H4" as "[H4|H4]".
        - iDestruct "H4" as "[Hprop_half x]".
          iDestruct (saved_prop_agree with "[$Hn2] [$Hprop_half]") as "#HQQi".
          iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq2".
          iMod ("Hinv_close" with "[Hoc H2 Hmap Hmap_bc Hgm Hgm_bc H3 Hn2 Hprop_half Hrecv_bc]") as "Hc".
          {
            iCombine "Hprop_half" "Hn2" as "H". iModIntro. iExists (chanstate.Closed []). iFrame. iExists Qs0. iSplitL ""; first done. iSplitL ""; first done. iFrame. iApply "H2".
            iFrame. iRight. unfold saved_prop_own. iFrame.
            replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1) by (rewrite dfrac_op_own; rewrite Qp.half_half; done).
            done.
          }
          iModIntro.
          iApply "HphiQ".
          iRewrite "Hp_eq2".
          done.
        - iDestruct "H4" as "Hprop_full".
          iCombine "Hn2 Hprop_full" as "Hbad".
          iDestruct (saved_prop_valid with "Hbad") as %Hvalid.
          exfalso.
          apply (Qp.not_add_le_l 1 (1/2)%Qp Hvalid).
      }
      done.
    }
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iFrame.
    destruct drain.
    {
      iIntros "Hoc".
      iMod "Hmask". iNamed "Hinv_open". iNamed "HNotified".
      iDestruct "HNotified" as "[Hn1 Hn2]".
      iDestruct (ghost_map_lookup with "Hmap Hn1") as %Hlookup.
      have Hi_lt : i < length Qs.
      {
        destruct (decide (i < length Qs)) as [H|Hge]; [exact H|].
        have Hge' : i ≥ length Qs by lia.
        rewrite (Hbound i Hge') in Hlookup. discriminate.
      }
      destruct (lookup_lt_is_Some_2 Qs i ltac:(lia)) as [x Hx].
      iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv") as "[H H2]".
      iNamed "H". iDestruct "H" as "[H3 H4]".
      iDestruct (ghost_map_elem_agree with "Hn1 H3") as %Heq.
      subst prop_gname0.
      iDestruct "H4" as "[H4|H4]".
      - iDestruct "H4" as "[Hprop_half x]".
        iDestruct (saved_prop_agree with "[$Hn2] [$Hprop_half]") as "#HQQi".
        iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq2".
        iMod ("Hinv_close" with "[Hoc H2 Hmap Hmap_bc Hgm Hgm_bc H3 Hn2 Hprop_half Hrecv_bc]") as "Hc".
        {
          iCombine "Hprop_half" "Hn2" as "H". iModIntro. iExists (chanstate.Closed []). iFrame.
          iExists Qs. iSplitL ""; first done. iSplitL ""; first done. iFrame. iApply "H2".
          iFrame. iRight. unfold saved_prop_own. iFrame.
          replace (DfracOwn (1 / 2) ⋅ DfracOwn (1 / 2)) with (DfracOwn 1) by (rewrite dfrac_op_own; rewrite Qp.half_half; done).
          done.
        }
        iModIntro.
        iApply "HphiQ".
        iRewrite "Hp_eq2".
        done.
      - iDestruct "H4" as "Hprop_full".
        iCombine "Hn2 Hprop_full" as "Hbad".
        iDestruct (saved_prop_valid with "Hbad") as %Hvalid.
        exfalso.
        apply (Qp.not_add_le_l 1 (1/2)%Qp Hvalid).
    }
    done.
  }
Qed.

Lemma wp_done_receive γ ch Q :
  {{{ is_done γ ch ∗
      Notified γ Q }}}
    chan.receive t #ch
  {{{ RET (#(zero_val V), #false); Q }}}.
Proof.
  iIntros (Φ) "(#Hdone & HNotified) Hcont".
  unfold is_done. iDestruct "Hdone" as "[#Hch #Hinv]".
   iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iApply ((done_receive_au _ _ _   ) with "[] [$HNotified] [Hcont] ").
  { unfold is_done. iFrame "#". }
  { iNext. iIntros "HQ". iApply "Hcont". iFrame. }
Qed.

Lemma done_receive_broadcast_au γ ch Q  `{!Persistent Q} :
  ∀ (Φ: V → bool → iProp Σ),
  is_done γ ch -∗
  BroadcastNotified γ Q -∗
  ▷ (Q -∗ Φ (zero_val V) false) -∗
  £1 ∗ £1 ∗ £1 ∗ £1 -∗
  recv_au γ.(chan_name) V (λ (v:V) (ok:bool), Φ v ok).
Proof.
  intros Φ.
  iIntros "#Hdone".
  iIntros "HBroadcastNotified".
  iIntros "HphiQ".
  iIntros "(? & ? & ? & ?)".
  unfold is_done. iDestruct "Hdone" as "[Hch Hinv]".
  
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch0".
  iNamed "Hinv_open".
  destruct s; try done.
  {
    iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iFrame.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc Hmap Hmap_bc]") as "_".
    {
      iNext. iFrame. iExists [], []. done.
    }
    iModIntro.
    unfold recv_nested_au.
    iInv "Hinv" as "Hinv_open1" "Hinv_close".
    iMod (lc_fupd_elim_later with "[$] Hinv_open1") as "Hinv_open1".
    iNamed "Hinv_open1".
    destruct s; try done.
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
    }
    {
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
      destruct drain.
      {
        iIntros "Hoc".
        iMod "Hmask". iNamed "Hinv_open1". iNamed "HBroadcastNotified".
        iDestruct "HBroadcastNotified" as "[Hn1 Hn2]".
        iDestruct (ghost_map_lookup with "Hmap_bc Hn1") as %Hlookup.
        have Hi_lt : i < length duplicableQs0.
        {
          destruct (lt_dec i (length duplicableQs0)) as [H|Hge]; [lia|].
          have Hge' : i ≥ length duplicableQs0 by lia.
          rewrite (Hbound_bc i Hge') in Hlookup. discriminate.
        }
        destruct (lookup_lt_is_Some_2 duplicableQs0 i ) as [x Hx].
        { lia. }
        iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv_bc") as "[H H2]".
        
        iNamed "H". iDestruct "H" as "(H3 & H4 & HQ)".
        
        iDestruct (ghost_map_elem_agree with "Hn1 H3") as %Heq.
        subst prop_gname0.
        iDestruct (saved_prop_agree with "[$Hn2] [$H4]") as "#HQQi".
        iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq2".
        iRewrite -"Hp_eq2" in "HQ".
iDestruct "HQ" as "#HQ".
iMod ("Hinv_close" with "[Hoc H2 Hmap Hmap_bc Hgm Hgm_bc H3 H4 HQ Hrecv]") as "Hc".
{
  iModIntro. iExists (chanstate.Closed []). iFrame. iExists  duplicableQs0. 
  iSplitL ""; first done. iSplitL ""; first done. iFrame.
        iRewrite "Hp_eq2" in "HQ".
  iApply "H2". iExists prop_gname. iFrame "#". iFrame. 
}
iModIntro.
iApply "HphiQ".
done.
       
}

      done.
    }
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
  }
  {
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext.
    iFrame.
    destruct drain.
    {
      iIntros "Hoc".
      iMod "Hmask". iNamed "Hinv_open". iNamed "HBroadcastNotified".
      iDestruct "HBroadcastNotified" as "[Hn1 Hn2]".
      iDestruct (ghost_map_lookup with "Hmap_bc Hn1") as %Hlookup.
      have Hi_lt : i < length duplicableQs.
      {
        destruct (lt_dec i (length duplicableQs)) as [H|Hge]; [lia|].
        have Hge' : i ≥ length duplicableQs by lia.
        rewrite (Hbound_bc i Hge') in Hlookup. discriminate.
      }
      destruct (lookup_lt_is_Some_2 duplicableQs i) as [x Hx].
      { lia. }
      iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv_bc") as "[H H2]".
      iNamed "H". iDestruct "H" as "(H3 & H4 & HQ)".
      iDestruct (ghost_map_elem_agree with "Hn1 H3") as %Heq.
      subst prop_gname0.
      iDestruct (saved_prop_agree with "[$Hn2] [$H4]") as "#HQQi".
      iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq2".
        iRewrite -"Hp_eq2" in "HQ".
iDestruct "HQ" as "#HQ".
      iMod ("Hinv_close" with "[Hoc H2 Hmap Hmap_bc Hgm Hgm_bc H3 H4 HQ Hrecv]") as "Hc".
      {
        iModIntro. iExists (chanstate.Closed []). iFrame.
        iExists duplicableQs. iSplitL ""; first done. iSplitL ""; first done. iFrame.
        iRewrite "Hp_eq2" in "HQ".
        iApply "H2". iExists prop_gname. iFrame "#". iFrame.
      }
      iModIntro.
      iApply "HphiQ".
      done.
    }
    done.
  }
Qed.

Lemma wp_done_receive_broadcast γ ch Q  `{!Persistent Q}:
  {{{ is_done γ ch ∗
      BroadcastNotified γ Q }}}
    chan.receive t #ch
  {{{ RET (#(zero_val V), #false); Q }}}.
Proof.
  iIntros (Φ) "(#Hdone & HBroadcastNotified) Hcont".
  unfold is_done. iDestruct "Hdone" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iApply ((done_receive_broadcast_au _ _ _) with "[] [$HBroadcastNotified] [Hcont]").
  { unfold is_done. iFrame "#". }
  { iNext. iIntros "HQ". iApply "Hcont". iFrame. }
Qed.

(* The lemmas below are for when you want receivers to gain exclusive ownership of something but 
also shared ownership of something else. This is likely very rarely necessary in practice. *)
Lemma done_receive_hybrid_au γ ch Q R `{!Persistent R} :
  ∀ (Φ: V → bool → iProp Σ),
  is_done γ ch -∗
  Notified γ Q -∗
  BroadcastNotified γ R -∗
  ▷ (Q -∗ R -∗ Φ (zero_val V) false) -∗
  £1 ∗ £1 ∗ £1 ∗ £1 -∗
  recv_au γ.(chan_name) V (λ (v:V) (ok:bool), Φ v ok).
Proof.
  intros Φ.
  iIntros "#Hdone HNotified HBroadcastNotified HphiQR (? & ? & ? & ?)".
  unfold is_done. iDestruct "Hdone" as "[Hch Hinv]".
  
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch0".
  iNamed "Hinv_open".
  destruct s; try done.
  {
    iFrame.
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
    iIntros "Hoc".
    iMod "Hmask" as "_".
    iMod ("Hinv_close" with "[Hoc Hmap Hmap_bc]") as "_".
    { iNext. iFrame. iExists [], []. done. }
    iModIntro.
    unfold recv_nested_au.
    iInv "Hinv" as "Hinv_open1" "Hinv_close".
    iMod (lc_fupd_elim_later with "[$] Hinv_open1") as "Hinv_open1".
    iNamed "Hinv_open1".
    destruct s; try done.
    - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"]. iNext. iFrame.
    - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"]. iNext. iFrame.
    - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
      iNext. iFrame.
      destruct drain; try done.
      iIntros "Hoc".
      iMod "Hmask". iNamed "Hinv_open1".
      
      iNamed "HNotified".
      iDestruct "HNotified" as "[Hn1 Hn2]".
      iDestruct (ghost_map_lookup with "Hmap Hn1") as %Hlookup.
      have Hi_lt : i < length Qs0.
      {
        destruct (lt_dec i (length Qs0)) as [H|Hge]; [lia|].
        have Hge' : i ≥ length Qs0 by lia.
        rewrite (Hbound i Hge') in Hlookup. discriminate.
      }
      destruct (lookup_lt_is_Some_2 Qs0 i) as [x Hx].
      { lia. }
      iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv") as "[HQ HQ_rest]".
      iNamed "HQ". iDestruct "HQ" as "[HQ_frag HQ_data]".
      iDestruct (ghost_map_elem_agree with "Hn1 HQ_frag") as %Heq_Q.
      subst prop_gname0.
      
      iNamed "HBroadcastNotified".
      iDestruct "HBroadcastNotified" as "[Hb1 Hb2]".
      iDestruct (ghost_map_lookup with "Hmap_bc Hb1") as %Hlookup_bc.
      have Hj_lt : i0 < length duplicableQs0.
      {
        destruct (lt_dec i0 (length duplicableQs0)) as [H|Hge]; [lia|].
        have Hge' : i0 ≥ length duplicableQs0 by lia.
        rewrite (Hbound_bc i0 Hge') in Hlookup_bc. discriminate.
      }
      destruct (lookup_lt_is_Some_2 duplicableQs0 i0 ) as [y Hy].
      { lia. }
      iDestruct (big_sepL_lookup_acc _ _ i0 y Hy with "Hrecv_bc") as "[HR HR_rest]".
      iNamed "HR". iDestruct "HR" as "(HR_frag & HR_saved & HR_data)".
      iDestruct (ghost_map_elem_agree with "Hb1 HR_frag") as %Heq_R.
      subst prop_gname0.
      
      iDestruct "HQ_data" as "[HQ_data|HQ_data]".
      + iDestruct "HQ_data" as "[HQ_half x]".
        iDestruct (saved_prop_agree with "Hn2 HQ_half") as "#HQQi".
        iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq_Q".
        
        iDestruct (saved_prop_agree with "Hb2 HR_saved") as "#HRRj".
        iMod (lc_fupd_elim_later with "[$] HRRj") as "#Hp_eq_R".
        
        iRewrite -"Hp_eq_R" in "HR_data".
        iDestruct "HR_data" as "#HR_data".
        
        iCombine "HQ_half Hn2" as "HQ_full".
        iRewrite -"Hp_eq_Q" in "x".
        iMod ("Hinv_close" with "[Hoc HQ_rest HR_rest Hmap Hmap_bc Hgm Hgm_bc HQ_frag HQ_full HR_frag HR_saved HR_data]") as "_".
        {
          iModIntro. iExists (chanstate.Closed []). iFrame.
          iExists Qs0, duplicableQs0.
          iSplitL ""; first done. iSplitL ""; first done.
          iFrame.
          iSplitL "HQ_rest HQ_frag HQ_full".
          {
            iApply "HQ_rest". iExists prop_gname. iFrame.
            iRight. unfold saved_prop_own.
            replace (DfracOwn (1/2) ⋅ DfracOwn (1/2)) with (DfracOwn 1) by 
              (rewrite dfrac_op_own; rewrite Qp.half_half; done).
            done.
          }
          {
            iRewrite "Hp_eq_R" in "HR_data".
            iApply "HR_rest". iExists prop_gname1. iFrame. iFrame "#".
          }
        }
        
        iModIntro.
        iApply "HphiQR" in "x".
        iApply "x". done.
      + iDestruct "HQ_data" as "HQ_full".
        iCombine "Hn2 HQ_full" as "Hbad".
        iDestruct (saved_prop_valid with "Hbad") as %Hvalid.
        exfalso. apply (Qp.not_add_le_l 1 (1/2)%Qp Hvalid).
  }
  - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"]. iNext. iFrame.
  - iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iNext. iFrame.
    destruct drain; try done.
    iIntros "Hoc".
    iMod "Hmask". iNamed "Hinv_open".
    
    iNamed "HNotified".
    iDestruct "HNotified" as "[Hn1 Hn2]".
    iDestruct (ghost_map_lookup with "Hmap Hn1") as %Hlookup.
    have Hi_lt : i < length Qs.
    {
      destruct (lt_dec i (length Qs)) as [H|Hge]; [lia|].
      have Hge' : i ≥ length Qs by lia.
      rewrite (Hbound i Hge') in Hlookup. discriminate.
    }
    destruct (lookup_lt_is_Some_2 Qs i) as [x Hx].
    { lia. }
    iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv") as "[HQ HQ_rest]".
    iNamed "HQ". iDestruct "HQ" as "[HQ_frag HQ_data]".
    iDestruct (ghost_map_elem_agree with "Hn1 HQ_frag") as %Heq_Q.
    subst prop_gname0.
    
    iNamed "HBroadcastNotified".
    iDestruct "HBroadcastNotified" as "[Hb1 Hb2]".
    iDestruct (ghost_map_lookup with "Hmap_bc Hb1") as %Hlookup_bc.
    have Hj_lt : i0 < length duplicableQs.
    {
      destruct (lt_dec i0 (length duplicableQs)) as [H|Hge]; [lia|].
      have Hge' : i0 ≥ length duplicableQs by lia.
      rewrite (Hbound_bc i0 Hge') in Hlookup_bc. discriminate.
    }
    destruct (lookup_lt_is_Some_2 duplicableQs i0) as [y Hy].
    { lia. }
    iDestruct (big_sepL_lookup_acc _ _ i0 y Hy with "Hrecv_bc") as "[HR HR_rest]".
    iNamed "HR". iDestruct "HR" as "(HR_frag & HR_saved & HR_data)".
    iDestruct (ghost_map_elem_agree with "Hb1 HR_frag") as %Heq_R.
    subst prop_gname0.
    
    iDestruct "HQ_data" as "[HQ_data|HQ_data]".
    + iDestruct "HQ_data" as "[HQ_half x]".
      iDestruct (saved_prop_agree with "Hn2 HQ_half") as "#HQQi".
      iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq_Q".
      
      iDestruct (saved_prop_agree with "Hb2 HR_saved") as "#HRRj".
      iMod (lc_fupd_elim_later with "[$] HRRj") as "#Hp_eq_R".
      
      iRewrite -"Hp_eq_R" in "HR_data".
      iDestruct "HR_data" as "#HR_data".
      
      iCombine "HQ_half Hn2" as "HQ_full".
        iRewrite -"Hp_eq_Q" in "x".
      iMod ("Hinv_close" with "[Hoc HQ_rest HR_rest Hmap Hmap_bc Hgm Hgm_bc HQ_frag HQ_full HR_frag HR_saved HR_data]") as "_".
      {
        iModIntro. iExists (chanstate.Closed []). iFrame.
        iExists Qs, duplicableQs.
        iSplitL ""; first done. iSplitL ""; first done.
        iFrame.
        iSplitL "HQ_rest HQ_frag HQ_full".
        {
          iApply "HQ_rest". iExists prop_gname. iFrame.
          iRight. unfold saved_prop_own.
          replace (DfracOwn (1/2) ⋅ DfracOwn (1/2)) with (DfracOwn 1) by 
            (rewrite dfrac_op_own; rewrite Qp.half_half; done).
          done.
        }
        {
          iRewrite "Hp_eq_R" in "HR_data".
          iApply "HR_rest". iExists prop_gname1. iFrame.
          iFrame "#".
        }
      }
      
      iModIntro.
      iApply "HphiQR" in "x".
      iApply "x".
      done.
    + iDestruct "HQ_data" as "HQ_full".
      iCombine "Hn2 HQ_full" as "Hbad".
      iDestruct (saved_prop_valid with "Hbad") as %Hvalid.
      exfalso. apply (Qp.not_add_le_l 1 (1/2)%Qp Hvalid).
Qed.

Lemma wp_done_receive_hybrid γ ch Q R `{!Persistent R}:
  {{{ is_done γ ch ∗
      Notified γ Q ∗
      BroadcastNotified γ R }}}
    chan.receive t #ch
  {{{ RET (#(zero_val V), #false); Q ∗ R }}}.
Proof.
  iIntros (Φ) "(#Hdone & HNotified & HBroadcastNotified) Hcont".
  unfold is_done. iDestruct "Hdone" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iApply (done_receive_hybrid_au with "[] [$HNotified] [$HBroadcastNotified] [Hcont]").
  { unfold is_done. iFrame "#". }
  { iNext. iIntros "HQ HR". iApply "Hcont". iFrame. }
Qed.

End done.