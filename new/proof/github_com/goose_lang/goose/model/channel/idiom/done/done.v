Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.
From New.golang.theory Require Import chan.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Import saved_prop.

(** * Done Channel Pattern Verification

    This file provides verification for the "done channel" pattern - a broadcast
    signaling mechanism where one sender closes the channel to notify multiple
    receivers, with each receiver obtaining their designated resources.

    Key features:
    - Single closer with exclusive Notify token
    - Multiple receivers with Notified tokens
    - Each receiver gets their specific resource upon channel close
    - Ghost state tracks: notify token + receiver map + saved propositions
*)

Section done.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `[!chan_idiomG Σ V].

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

Record done_names := {
  chan_name : chan_names;
  receivers_map_name : gname;
  acc_name         : gname
}.

Definition NotifyInternal (γ : done_names) (Qs : list (iProp Σ)) : iProp Σ :=
  ∃ (m : gmap nat gname),
    ghost_map_auth γ.(receivers_map_name) (1/2) m ∗
    ⌜∀ i, i ≥ length Qs → m !! i = None⌝ ∗
    [∗ list] i ↦ Q ∈ Qs,
      ∃ (prop_gname : gname),
        i ↪[γ.(receivers_map_name)]{#1/2} prop_gname ∗
        saved_prop_own prop_gname (DfracOwn(1/2)) Q.

Definition Notify (γ : done_names) (R : iProp Σ) : iProp Σ :=
  ∃ Qs, NotifyInternal γ Qs ∗ saved_prop_own γ.(acc_name) (DfracOwn 1) R
∗ (R -∗ [∗ list] Q ∈ Qs, Q) .

Definition Notified (γ : done_names) (Q : iProp Σ) : iProp Σ :=
  ∃ prop_gname i,
    i ↪[γ.(receivers_map_name)]{#1/2} prop_gname ∗
    saved_prop_own prop_gname (DfracOwn (1/2)) Q.

Definition is_done (γ : done_names) (ch : loc) : iProp Σ :=
  is_chan ch γ.(chan_name) V ∗
  inv nroot (
    ∃ s (m : gmap nat gname) (Qs: list (iProp Σ)),
      "Hch" ∷ own_chan γ.(chan_name) V s ∗
      "Hmap" ∷ ghost_map_auth γ.(receivers_map_name) (1/2)%Qp m ∗
      match s with
      | chanstate.Idle => True
      | chanstate.RcvPending => True
      | chanstate.Closed [] =>
          "%Hbound" ∷ ⌜∀ i, i ≥ length Qs → m !! i = None⌝ ∗
          "Hgm" ∷ ghost_map_auth γ.(receivers_map_name) (1/2)%Qp m ∗
          "Hrecv" ∷
            ([∗ list] i ↦ Q ∈ Qs,
              ∃ prop_gname,
                i ↪[γ.(receivers_map_name)]{#1/2} prop_gname ∗
                (((saved_prop_own prop_gname (DfracOwn (1/2)) Q) ∗ Q) ∨
                 ((saved_prop_own prop_gname (DfracOwn (1)) Q))))
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
  iDestruct "HNotifyInternal" as (Qs) "(HQs & Hsp & HRQs)".
  iDestruct "Hdone" as "[#Hch #Hinv]".
  iMod (saved_prop_alloc Q (DfracOwn 1)) as (prop_gname) "Hprop"; first done.
  iDestruct "Hprop" as "[Hprop1 Hprop2]".
  set (i := length Qs).
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  unfold NotifyInternal.
  iNamed "HQs".
  iDestruct "HQs" as "(Hauth_half & %H & HQs)".
  iDestruct "Hinv_open" as (s m' Qs') "(>Hch_own & >Hmap_half & Hstate)".
  iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m m') with "[$Hauth_half] [$Hmap_half]") as %->.
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
  - (* keep the old part as-is *)
    rewrite big_sepL_singleton.
    iFrame.
    replace (length Qs + 0) with (length Qs) by done.
    iFrame.

}
iMod (saved_prop_update (R ∗ Q) with "Hsp") as "Hsp".
  destruct s; try iDestruct "Hstate" as ">Hstate"; try done.
  {
    iMod ("Hinv_close" with "[Hch_own Hauth_half2 Hstate]").
    {
      iNext. iExists chanstate.Idle. iExists (<[i := prop_gname]> m'). iFrame. iExists [].
      done.
    }
    {
      iModIntro. iFrame. subst i. iSplitL "".
      {
        iPureIntro. intros j Hj.
        rewrite length_app /= in Hj.
        destruct (decide (j = length Qs)) as [->|Hne].
        - lia.
        - rewrite lookup_insert_ne; last done.
          apply H. lia.
      }
      replace (length Qs + 0) with (length Qs) by lia.
      iIntros "[HR' HQ]".
      iFrame. simpl. iSplitL "HR' HRQs".
      {
      iApply "HRQs".
      done.
      }
      done.
    }
  }
  {
    iMod ("Hinv_close" with "[Hch_own Hauth_half2 Hstate]").
    {
      iNext. iFrame.
      iExists []. done.
    }
    {
      iModIntro. iFrame.
      replace (length Qs + 0) with (length Qs) by lia.
      iFrame.
      iSplitL "". { iPureIntro.
 intros.
      subst i.
      rewrite length_app in H0; simpl in H0.
      assert (Hi0_ne : i0 ≠ length Qs) by lia.
      assert (Hi0_ge : i0 ≥ length Qs) by lia.
      rewrite lookup_insert_ne.
      { apply H. done. }
      done.
      }
       iIntros "[HR' HQ]".
      iFrame. simpl. iSplitL "HRQs HR'".
      {
      iApply "HRQs".
      done.
      }
      done.

    }
  }
  {
    destruct drain.
    - iDestruct "Hstate" as "[>%Hc Hgm]".
      iDestruct "Hgm" as "(>? & ?)". iNamed.
      iDestruct ((ghost_map_auth_agree _ (1/2) (1/2) m' (<[i:=prop_gname]> m')) with "[$Hgm] [$Hauth_half1]") as %->.
      iCombine "Hauth_half2 Hauth_half1" as "Hgm2".
      iDestruct ((ghost_map_auth_agree) with "[$Hgm] [$Hgm2]") as %->.
      iDestruct (ghost_map_auth_valid with "Hgm2") as %Hvalid1.
      iDestruct (ghost_map_auth_valid_2 with "Hgm2 Hgm") as %[Hvalid2 _].
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
  iMod (ghost_map_alloc_empty) as (γmap) "[Hmap_auth1 Hmap_auth2]".
  iMod (saved_prop_alloc (emp : iProp Σ) (DfracOwn 1)) as (γacc) "Hacc_full".
  {
    done.
  }
  set (γdone := {|
    chan_name := γ;
    receivers_map_name := γmap;
    acc_name := γacc

  |}).
  iMod (inv_alloc nroot _ (
    ∃ s m Qs,
      "Hch" ∷ own_chan γ V s ∗
      "Hmap" ∷ ghost_map_auth γmap (1/2)%Qp m ∗
      match s with
      | chanstate.Idle => True
      | chanstate.RcvPending => True
      | chanstate.Closed [] =>
          "%Hbound" ∷ ⌜∀ i, i ≥ length Qs → m !! i = None⌝ ∗
          "Hgm" ∷ ghost_map_auth γmap (1/2)%Qp m ∗
          "Hrecv" ∷
            ([∗ list] i ↦ Q ∈ Qs,
              ∃ prop_gname,
                i ↪[γmap]{#1/2} prop_gname ∗
                (((saved_prop_own prop_gname (DfracOwn (1/2)) Q) ∗ Q) ∨
                 ((saved_prop_own prop_gname (DfracOwn (1)) Q))))
      | _ => False
      end
  )%I with "[Hoc Hmap_auth1]") as "#Hinv".
  {
    iNext. iExists chanstate.Idle, ∅.
    iFrame. iExists []. done.
  }
  iModIntro. iExists γdone. iFrame "#".
  rewrite /NotifyInternal. replace (γdone.(chan_name)) with γ by done. iFrame.
  replace (γdone.(receivers_map_name)) with γmap by done. iFrame.
  iDestruct (big_sepL_nil (λ i Q, ∃ prop_gname : gname, i ↪[γmap]{#1 / 2} prop_gname ∗ saved_prop_own prop_gname (DfracOwn (1 / 2)) Q)%I) as "H".
  iExists [].
  iSplitR "".
  {


  iFrame.
  iSplitL "". { iFrame. iPureIntro. done. }
  simpl.
  done.
  }
  {
    simpl. done.
  }
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
  iDestruct "HProps" as "(Hgm & %Hlen & HQs)".
  unfold is_done. iDestruct "Hdone" as "[Hch Hinv]". iIntros "Hcont".
  iMod (lc_fupd_elim_later with "[$] Hcont") as "Hcont".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iDestruct "Hinv_open" as (s m' Qs') "(Hch_own & Hmap_half & Hstate)".
  iDestruct (ghost_map_auth_agree with "Hgm Hmap_half") as %->.
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.
  destruct s; try done.
  - iIntros "Hoc".
    iMod "Hmask".
    iMod (lc_fupd_elim_later with "[$] Hinv_close") as "Hinv_close".
    iDestruct "Hsp" as "[Hsp Hrs]".
    iApply "Hrs" in "HR".
    iMod ("Hinv_close" with "[Hmap_half Hsp Hoc HR Hgm HQs]") as "_".
    {
      iNext. iExists (chanstate.Closed []), m'. iFrame "Hmap_half".
      iFrame. iExists Qs.
      iSplitL "". { iPureIntro. done. }

      iDestruct ((big_sepL_sep_2) with "[$HR] [$HQs]") as "H".
      iFrame.
      iApply (big_sepL_mono with "H").
      {
        iIntros (k). iIntros (y). iIntros "%H". iIntros "H". iDestruct "H" as "[H y]".
        iFrame. iNamed "H". iNamed "y". iExists prop_gname. iDestruct "y" as "[H1 H2]".
        iFrame. iLeft. iFrame.
      }
    }
    iModIntro. iApply "Hcont".
  - destruct drain; try done.
    iNamed "Hstate".
    iCombine "Hmap_half Hgm" as "H". iNamed "Hstate".
    iCombine "H Hgm" as "H".
    iDestruct (ghost_map_auth_valid with "H") as %Hvalid1.
    exfalso.
    eapply (Qp.not_add_le_l 1 (1/2)%Qp).
    exact Hvalid1.
Qed.

Lemma wp_done_close γ ch R `[ct ↓u go.ChannelType dir t]:
  {{{ is_done γ ch ∗
      Notify γ R ∗ R }}}
    #(functions go.close [ct]) #ch
  {{{ RET #(); True }}}.
Proof using All.
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
    iMod ("Hinv_close" with "[Hoc Hmap]") as "_".
    {
      iNext. iFrame. iExists []. done.
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
          destruct (lt_dec i (length Qs0)) as [H|Hge]; [exact H|].
          have Hge' : i ≥ length Qs0 by lia.
          rewrite (Hbound i Hge') in Hlookup. discriminate.
        }
        destruct (lookup_lt_is_Some_2 Qs0 i Hi_lt) as [x Hx].
        iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv") as "[H H2]".
        iNamed "H". iDestruct "H" as "[H3 H4]".
        iDestruct (ghost_map_elem_agree with "Hn1 H3") as %Heq.
        subst prop_gname0.
        iDestruct "H4" as "[H4|H4]".
        - iDestruct "H4" as "[Hprop_half x]".
          iDestruct (saved_prop_agree with "[$Hn2] [$Hprop_half]") as "#HQQi".
          iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq2".
          iMod ("Hinv_close" with "[Hoc H2 Hmap Hgm H3 Hn2 Hprop_half]") as "Hc".
          {
            iCombine "Hprop_half" "Hn2" as "H". iModIntro. iExists (chanstate.Closed []). iFrame. iExists Qs0. iSplitL ""; first done. iFrame. iApply "H2".
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
        destruct (lt_dec i (length Qs)) as [H|Hge]; [exact H|].
        have Hge' : i ≥ length Qs by lia.
        rewrite (Hbound i Hge') in Hlookup. discriminate.
      }
      destruct (lookup_lt_is_Some_2 Qs i Hi_lt) as [x Hx].
      iDestruct (big_sepL_lookup_acc _ _ i x Hx with "Hrecv") as "[H H2]".
      iNamed "H". iDestruct "H" as "[H3 H4]".
      iDestruct (ghost_map_elem_agree with "Hn1 H3") as %Heq.
      subst prop_gname0.
      iDestruct "H4" as "[H4|H4]".
      - iDestruct "H4" as "[Hprop_half x]".
        iDestruct (saved_prop_agree with "[$Hn2] [$Hprop_half]") as "#HQQi".
        iMod (lc_fupd_elim_later with "[$] HQQi") as "#Hp_eq2".
        iMod ("Hinv_close" with "[Hoc H2 Hmap Hgm H3 Hn2 Hprop_half]") as "Hc".
        {
          iCombine "Hprop_half" "Hn2" as "H". iModIntro. iExists (chanstate.Closed []). iFrame.
          iExists Qs. iSplitL ""; first done. iFrame. iApply "H2".
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
Proof using All.
  iIntros (Φ) "(#Hdone & HNotified) Hcont".
  unfold is_done. iDestruct "Hdone" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch γ.(chan_name) with "[$Hch]").
  iApply ((done_receive_au _ _ _   ) with "[] [$HNotified] [Hcont] ").
  { unfold is_done. iFrame "#". }
  { iNext. iIntros "HQ". iApply "Hcont". iFrame. }
Qed.

End done.
