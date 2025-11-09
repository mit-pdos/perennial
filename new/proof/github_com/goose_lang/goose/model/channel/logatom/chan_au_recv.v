From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.

#[local] Transparent is_channel own_channel.

Section atomic_specs.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_TryReceive (ch: loc) (cap: Z)  (γ: chan_names) :
  ∀ Φ ,
  is_channel ch cap γ -∗
  rcv_au_slow ch cap γ (λ v ok, Φ (#true, #v, #ok)%V) ∧ Φ (#false, #(default_val V), #true)%V -∗
  WP channel.Channel__TryReceiveⁱᵐᵖˡ #ch #t #true {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "HΦ".
  wp_call_lc "?".
  iNamed "Hunb".
  wp_auto_lc 9.
  wp_call.
  wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  (* Case analysis on channel state *)
  destruct s.
  - (* Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      destruct buff as [|v rest].
      {
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        rewrite length_nil in Hl.
        replace (sint.Z slice_val.(slice.len_f))with (0) in * by word.
        word.
      }
      iLeft in "HΦ".
      iAssert (own_channel ch cap (chan_rep.Buffered (v :: rest)) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      unfold rcv_au_fast.
      iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iDestruct (own_channel_agree with "Hown Hoc") as %Heq.
      subst s.
      iMod (own_channel_halves_update (chan_rep.Buffered rest) with "Hown Hoc")
        as "[Hown1 Hown2]".
      { done. }
      iMod ("Hcont" with "Hown1") as "Hcont".
      iModIntro.
      have Hpos : 0 ≤ sint.Z (W64 0) by word.
      have Hlookup0 : (v :: rest) !! 0%nat = Some v by done.
      iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
      { exact Hpos. }
      { done. }
      iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
      iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
      assert (0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len_f)) as Hlt.
      { word. }
      wp_auto.
      wp_apply ((wp_load_slice_elem slice_val 0
                   ( <[0%nat:=v]> (v :: rest)))
                 with "[Hclose]"). all: try word.
      { iFrame. done. }
      iIntros "Hsl". wp_auto.
      iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
      wp_apply (wp_slice_slice_pure).
      { iPureIntro. word. }
      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state slice_cap Hsl buffer Hown2  $Hlock]").
      { unfold chan_inv_inner. iExists (Buffered rest). iFrame.

        change (sint.Z (W64 0)) with 0 in *.
        (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
        simpl.
        iDestruct (own_slice_split_all (W64 1) with "Hsl")
          as "[Hhd Htail]"; first word. simpl.
        iFrame.
        iDestruct (own_slice_len with "Hhd") as %[Hlent _].
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
        iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
        { word. }
        iApply "H" in "slice_cap". iFrame.
      }
      done.
    }
    {
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      assert ( sint.Z slice_val.(slice.len_f) = sint.Z (W64 0)).
      {
        destruct (sint.Z slice_val.(slice.len_f)). all: try done.
      }
      assert (buff = []).
      { destruct buff. { done. } { rewrite H in Hl. naive_solver. } }
      subst buff.

      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state buffer slice slice_cap Hchanrepfrag $Hlock]").
      { iFrame. unfold chan_inv_inner. iFrame.  iExists (Buffered []).
        iFrame. iPureIntro. done. }
      iRight in "HΦ". iFrame.
    }
  - iNamed "phys". wp_auto_lc 5.
    iNamed "offer".
    iDestruct (offer_idle_to_recv with "Hoffer") as ">[offer1 offer2]".
    iMod ((saved_prop.saved_pred_update (K (λ (v0 : V) (ok : bool), Φ (# true, # v0, # ok)%V)
          )) with "Hpred") as "[Hpred1 Hpred2]".
    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer  offer1 Hpred1 Hchanrepfrag HΦ $Hlock]").
    { unfold chan_inv_inner. iExists (RcvWait).
      iFrame "offer1". (* FIXME: iFrame frames random junk into ?Goal4. *)
      iFrame "HΦ". iFrame. iSplitL; last done.
      iIntros "H". iLeft in "H". iFrame. }
    wp_call.
    wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan".
    iNamed "phys". iNamed "offer".
    destruct s.
    {
      iNamed "phys". wp_auto_lc 5.
      unfold chan_cap_valid in Hcapvalid. subst cap.
      iNamed "offer".
      unfold chan_cap_valid in Hcapvalid. done.
    }
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      unfold offer_bundle_empty.
      iExFalso.
      iApply (saved_offer_half_full_invalid with "offer2 Hoffer").

    }
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      discriminate Heq.

    }
    {
      unfold chan_phys. iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iDestruct (offer_bundle_lc_agree with "[$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      iMod ((saved_prop.saved_pred_update_halves (K Φr0)
            ) with "Hpred2 Hpred") as "[Hpred1 Hpred2]".
      iCombine "Hpred1 Hpred2" as "Hp".
      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state v slice slice_cap buffer Hchanrepfrag   Hp  H1   $Hlock]").
      { unfold chan_inv_inner. iExists (Idle). iFrame.
        iExists Φr0. iFrame. unfold  saved_prop.saved_pred_own . rewrite dfrac_op_own Qp.half_half.
        iFrame.
        done.
      }
      iRewrite -"Hpeq" in "HP".
      iRight in "HP". iFrame.
    }
    {
      iNamed "phys". wp_auto_lc 5.
      iNamed "offer".

      unfold rcv_au_inner.
      iApply fupd_wp.
      iMod "Hau".
      iMod (lc_fupd_elim_later with "[$] Hau") as "HP".
      iNamed "HP".
      iAssert (own_channel ch cap (chan_rep.SndCommit v0) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Hseq". subst s.
      iDestruct (own_channel_halves_update (chan_rep.Idle)
                  with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
      { done. }
      iMod ("Hcontinner" with "Hgv1") as "Hcont".
      iModIntro.
      iDestruct (saved_prop.saved_pred_agree γ.(offer_parked_pred_name)
                                                 (DfracOwn (1/2)) (DfracOwn (1/2))
                                                 (K (λ (v1 : V) (ok : bool), Φ (# true, # v1, # ok)%V))
                                                 (K Φr0)
                                                 (v0, true)
                  with "[$Hpred2] [$Hpred]") as "#Hagree".
      iCombine "Hpred2 Hpred" as "offer".
      rewrite dfrac_op_own Qp.half_half.
      iDestruct (offer_bundle_lc_agree with "[$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state v slice slice_cap buffer H1   Hgv2 offer   $Hlock]").
      { unfold chan_inv_inner. iExists (Idle). iFrame.
      }
      unfold K.
      iRewrite -"Hagree" in "Hcont". done.
    }
    {
      iNamed "phys". wp_auto.
      iNamed "offer".
      iExFalso.
      iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      discriminate Heq.

    }
    {
      iNamed "phys". unfold chan_phys.
      destruct draining.
      {
        iNamed "phys". wp_auto.

        iNamed "offer". unfold chan_logical. iDestruct "offer" as "[Ho Hoffer]".
        iNamed "Hoffer". unfold chan_cap_valid in Hcapvalid. subst cap. simpl.
        iExFalso.
        iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
        discriminate Heq.
      }
      {
        iNamed "phys". wp_auto.
        iNamed "offer".
        iExFalso.
        unfold chan_cap_valid in *. subst cap. done.
      }
    }
  - (* Idle unbuffered channel  *)
    iNamed "phys". wp_auto.
    iNamed "offer".
    iApply "Hau" in "HP".
    unfold send_au_slow.
    iApply fupd_wp. iMod "HP".
    iMod (lc_fupd_elim_later with "[$] HP") as "HP". iNamed "HP".
    iDestruct "Hoc" as "[H1 H2]".
    iDestruct (chan_rep_agree with "[$H1] [$Hchanrepfrag]") as "%Hseq". subst s.
    iAssert (own_channel ch cap (chan_rep.Idle) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame. iPureIntro. done. }
    iAssert (own_channel ch cap (chan_rep.Idle) γ)%I
      with "[H1]" as "Hown1".
    { iFrame. iPureIntro. done. }
    iDestruct (own_channel_halves_update (chan_rep.SndPending v)
                with "[$Hown] [$Hown1]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont1". iModIntro.
    iApply fupd_wp. iLeft in "HΦ". iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HP".
    iNamed "HP".
    iDestruct (own_channel_agree with "[$Hgv1] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update (chan_rep.RcvCommit)
                with "[$Hgv1] [$Hoc]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont". iModIntro.
    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer Hgv1 H2 Hpred Hoffer Hcont1 $Hlock]").
    { unfold chan_inv_inner.  iExists (RcvDone v). iFrame. iNamed "Hgv1". iFrame.
    }
    done.
  - iNamed "phys". wp_auto.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists RcvWait. iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys". wp_auto.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v). iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys". wp_auto.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v). iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys".
    destruct draining.
    { iNamed "offer".
      unfold chan_logical.
      iNamed "phys".
      wp_auto_lc 2.
      iApply fupd_wp. iLeft in "HΦ". iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ". unfold chan_logical. iDestruct "offer" as "[offer H]".
      iDestruct (own_channel_agree with "[$offer] [$Hoc]") as "%Hseq". subst s.

      iMod ("Hcont" with "Hoc") as "Hcont". iModIntro.
      wp_if_destruct.
      {
        iDestruct (own_slice_len with "slice") as "[%H1 %H2]".
        simpl in H1.
        word.
      }

      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state  slice slice_cap buffer offer H $Hlock]").
      { unfold chan_inv_inner.  iExists (Closed []). iFrame.
      }
      done.
    }
    {
      iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
      wp_if_destruct.
      {
        iLeft in "HΦ".
        iAssert (own_channel ch cap (chan_rep.Closed (v :: draining)) γ)%I
          with "[Hchanrepfrag]" as "Hown".
        { iFrame. iPureIntro. done. }
        iApply fupd_wp.
        iMod "HΦ".
        iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
        iNamed "HΦ".
        iDestruct (own_channel_agree with "Hown Hoc") as %Heq.
        subst s.
        iMod (own_channel_halves_update (chan_rep.Closed draining) with "Hown Hoc")
          as "[Hown1 Hown2]".
        { simpl. destruct draining; auto. }
        iMod ("Hcont" with "Hown1") as "Hcont".
        iModIntro.
        have Hpos : 0 ≤ sint.Z (W64 0) by word.
        have Hlookup0 : (v :: draining) !! 0%nat = Some v by done.
        iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
        { exact Hpos. }
        { done. }
        iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
        iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
        have Hlt : 0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len_f).
        { move: Hlen_eq; simpl.  (* length (v::draining) = S (length draining) *)
          (* sint.nat len = S _  ⇒  sint.Z len > 0 *)
          word. }
        wp_auto.
        wp_apply ((wp_load_slice_elem slice_val 0
                     ( <[sint.nat (W64 0):=v]> (v :: draining)))
                   with "[Hclose]"). all: try word.
        { iFrame. done. }
        iIntros "Hsl". wp_auto.
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
        wp_apply (wp_slice_slice_pure).
        { iPureIntro. word. }
        wp_call.
        wp_apply (wp_lock_unlock
                   with "[$lock state slice_cap Hsl buffer Hown2  $Hlock]").
        { unfold chan_inv_inner. iExists (Closed draining). iFrame.

          have -> : sint.nat (W64 0) = 0%nat by word.
          (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
          simpl.
          iDestruct (own_slice_split_all (W64 1) with "Hsl")
            as "[Hhd Htail]"; first word. simpl.
          iFrame.
          iDestruct (own_slice_len with "Hhd") as %[Hlent _].
          iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
          iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
          { word. }
          iApply "H" in "slice_cap". iFrame.
          destruct draining.
          {
            iFrame. destruct cap; done.
          }
          { iFrame. }
        }
        done.
      }
      {
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        assert (sint.Z slice_val.(slice.len_f) = sint.Z (W64 0)).
        {
          word.
        }
        replace (sint.nat slice_val.(slice.len_f)) with 0%nat in *.
        { done.  }
        word.
      }
    }
Qed.

Lemma wp_Receive (ch: loc) (cap: Z) (γ: chan_names) :
  ∀ Φ,
  is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ rcv_au_slow ch cap γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP channel.Channel__Receiveⁱᵐᵖˡ #ch #t #() {{ Φ }}.
Proof.
  intros. iIntros "#Hic". iIntros "Hau".
  iDestruct (is_channel_not_null with "[$Hic]") as "%Hnn".
  wp_call_lc "?".
  wp_auto_lc 3.
  iSpecialize ("Hau" with "[$]").

  wp_if_destruct; first done.
  wp_for. iNamed "Hau".
  wp_apply (wp_TryReceive ch cap γ with "[$]").
  iSplit.
  { iFrame.
    unfold rcv_au_slow. iMod "Hau".
    iModIntro. iModIntro. iNamed "Hau". iFrame.
    destruct s; try done.
    - destruct buff;first done.
      iIntros "H". iMod ("Hcont" with "H") as "H".
      iModIntro. wp_auto. wp_for_post.
      iFrame.
    - iIntros "H". iMod ("Hcont" with "H") as "H".
      iModIntro. unfold rcv_au_inner.  iMod "H". iModIntro. iModIntro.
      iNamed "H".
      iFrame.
      destruct s; try done.
      {
        iIntros "Hcontineer".
        iMod ("Hcontinner" with "Hcontineer") as "H". iModIntro. wp_auto.
        wp_for_post. done.
      }
      {
        destruct draining; try done.
        iIntros "Hcontineer".
        iMod ("Hcontinner" with "Hcontineer") as "H". iModIntro. wp_auto.
        wp_for_post. done.

      }
    - iIntros "Hcontineer".
      iMod ("Hcont" with "Hcontineer") as "H". iModIntro. wp_auto.
      wp_for_post. done.
    - destruct draining; try done.
      {
        iIntros "Hcontineer".
        iMod ("Hcont" with "Hcontineer") as "H". iModIntro. wp_auto.
        wp_for_post. done.
      }
      {
        iIntros "Hcontineer".
        iMod ("Hcont" with "Hcontineer") as "H". iModIntro. wp_auto.
        wp_for_post. done.
      }
  }
  wp_auto. wp_for_post. iFrame.
Qed.

Lemma wp_TryReceive_nb (ch: loc) (cap: Z)  (γ: chan_names) :
  ∀ Φ ,
  is_channel ch cap γ -∗
  rcv_au_fast ch cap γ (λ v ok, Φ (#true, #v, #ok)%V) ∧ Φ (#false, #(default_val V), #true)%V -∗
  WP channel.Channel__TryReceiveⁱᵐᵖˡ #ch #t #false {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "HΦ".
  wp_call_lc "?".
  iNamed "Hunb".
  wp_auto_lc 9.
  wp_call.
  wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s.
  - (* Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      destruct buff as [|v rest].
      {
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        rewrite length_nil in Hl.
        replace (sint.Z slice_val.(slice.len_f))with (0) in * by word.
        word.
      }
      iLeft in "HΦ".
      iAssert (own_channel ch cap (chan_rep.Buffered (v :: rest)) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      unfold rcv_au_fast.
      iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iDestruct (own_channel_agree with "Hown Hoc") as %Heq.
      subst s.
      iMod (own_channel_halves_update (chan_rep.Buffered rest) with "Hown Hoc")
        as "[Hown1 Hown2]".
      { done. }
      iMod ("Hcont" with "Hown1") as "Hcont".
      iModIntro.
      have Hpos : 0 ≤ sint.Z (W64 0) by word.
      have Hlookup0 : (v :: rest) !! 0%nat = Some v by done.
      iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
      { exact Hpos. }
      { done. }
      iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
      iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
      have Hlt : 0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len_f).
      { move: Hlen_eq; simpl.  (* length (v::draining) = S (length draining) *)
        (* sint.nat len = S _  ⇒  sint.Z len > 0 *)
        word. }
      wp_auto.
      wp_apply ((wp_load_slice_elem slice_val 0
                   ( <[sint.nat (W64 0):=v]> (v :: rest)))
                 with "[Hclose]"). all: try word.
      { iFrame. done. }
      iIntros "Hsl". wp_auto.
      iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
      wp_apply (wp_slice_slice_pure).
      { iPureIntro. word. }
      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state slice_cap Hsl buffer Hown2  $Hlock]").
      { unfold chan_inv_inner. iExists (Buffered rest). iFrame.

        have -> : sint.nat (W64 0) = 0%nat by word.
        (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
        simpl.
        iDestruct (own_slice_split_all (W64 1) with "Hsl")
          as "[Hhd Htail]"; first word. simpl.
        iFrame.
        iDestruct (own_slice_len with "Hhd") as %[Hlent _].
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
        iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
        { word. }
        iApply "H" in "slice_cap". iFrame.
      }
      done.
    }
    {
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      assert ( sint.Z slice_val.(slice.len_f) = sint.Z (W64 0)).
      {
        destruct (sint.Z slice_val.(slice.len_f)). all: try done.
      }
      assert (buff = []).
      { destruct buff. { done. } { rewrite H in Hl. naive_solver. } }
      subst buff.
      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state buffer slice slice_cap Hchanrepfrag $Hlock]").
      { iFrame. unfold chan_inv_inner. iFrame.  iExists (Buffered []).
        iFrame. iPureIntro. done. }
      iRight in "HΦ". iFrame.
    }
  - iNamed "phys". wp_auto_lc 2.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists Idle. iFrame. }
    iRight in "HΦ". iFrame.
  - (* Idle unbuffered channel  *)
    iNamed "phys". wp_auto_lc 2.
    iNamed "offer".
    iApply fupd_wp. iApply "Hau" in "HP". iMod "HP".
    iMod (lc_fupd_elim_later with "[$] HP") as "HP". iNamed "HP".
    iDestruct "Hoc" as "[H1 H2]".
    iDestruct (chan_rep_agree with "[$H1] [$Hchanrepfrag]") as "%Hseq". subst s.
    iAssert (own_channel ch cap (chan_rep.Idle) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame. iPureIntro. done. }
    iAssert (own_channel ch cap (chan_rep.Idle) γ)%I
      with "[H1]" as "Hown1".
    { iFrame. iPureIntro. done. }
    iDestruct (own_channel_halves_update (chan_rep.SndPending v)
                with "[$Hown] [$Hown1]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont1". iModIntro.
    iLeft in "HΦ".
    iApply fupd_wp.
    iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ".
    iDestruct (own_channel_agree with "[$Hgv1] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update (chan_rep.RcvCommit)
                with "[$Hgv1] [$Hoc]") as ">[Hgv1 Hgv2]".
    { done. }

    iMod ("Hcont" with "Hgv2") as "Hcont". iModIntro.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer Hgv1 H2 Hpred Hoffer Hcont1 $Hlock]").
    { unfold chan_inv_inner.  iExists (RcvDone v). iFrame. iNamed "Hgv1". iFrame.
    }
    done.
  - iNamed "phys". wp_auto_lc 2.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists RcvWait. iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys". wp_auto_lc 2.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v). iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys". wp_auto_lc 2.

    wp_call.
    wp_apply (wp_lock_unlock
               with "[$lock state v slice slice_cap buffer offer  $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v). iFrame. }
    iRight in "HΦ". iFrame.
  - iNamed "phys".
    destruct draining.
    { iNamed "offer". iNamed "phys".
      wp_auto_lc 2.
      iApply fupd_wp. iLeft in "HΦ". iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      unfold chan_logical. iDestruct "offer" as "[offer H]".
      iDestruct (own_channel_agree with "[$offer] [$Hoc]") as "%Hseq". subst s.

      iMod ("Hcont" with "Hoc") as "Hcont". iModIntro.
      wp_if_destruct.
      {
        iDestruct (own_slice_len with "slice") as "[%H1 %H2]".
        simpl in H1.
        word.
      }

      wp_call.
      wp_apply (wp_lock_unlock
                 with "[$lock state  slice slice_cap buffer H offer $Hlock]").
      { unfold chan_inv_inner.  iExists (Closed []). iFrame.
      }
      done.
    }
    {
      iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
      wp_if_destruct.
      {

        iLeft in "HΦ".
        iAssert (own_channel ch cap (chan_rep.Closed (v :: draining)) γ)%I
          with "[Hchanrepfrag]" as "Hown".
        { iFrame. iPureIntro. done. }
        iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
        unfold rcv_au_fast.
        iApply fupd_wp.
        iMod "HΦ".
        iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
        iNamed "HΦ".
        iDestruct (own_channel_agree with "Hown Hoc") as %Heq.
        subst s.
        iMod (own_channel_halves_update (chan_rep.Closed draining) with "Hown Hoc")
          as "[Hown1 Hown2]".
        { simpl. destruct draining; auto. }
        iMod ("Hcont" with "Hown1") as "Hcont".
        iModIntro.
        have Hpos : 0 ≤ sint.Z (W64 0) by word.
        have Hlookup0 : (v :: draining) !! 0%nat = Some v by done.
        iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
        { exact Hpos. }
        { done. }
        iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
        iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
        have Hlt : 0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len_f).
        { move: Hlen_eq; simpl.  (* length (v::draining) = S (length draining) *)
          (* sint.nat len = S _  ⇒  sint.Z len > 0 *)
          word. }
        wp_auto.
        wp_apply ((wp_load_slice_elem slice_val 0
                     ( <[sint.nat (W64 0):=v]> (v :: draining)))
                   with "[Hclose]"). all: try word.
        { iFrame. done. }
        iIntros "Hsl". wp_auto.
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
        wp_apply (wp_slice_slice_pure).
        { iPureIntro. word. }
        wp_call.
        wp_apply (wp_lock_unlock
                   with "[$lock state slice_cap Hsl buffer Hown2  $Hlock]").
        { unfold chan_inv_inner. iExists (Closed draining). iFrame.

          change (sint.nat (W64 0)) with 0%nat in *.
          (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
          simpl.
          iDestruct (own_slice_split_all (W64 1) with "Hsl")
            as "[Hhd Htail]"; first word. simpl.
          iFrame.
          iDestruct (own_slice_len with "Hhd") as %[Hlent _].
          iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
          iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
          { word. }
          iApply "H" in "slice_cap". iFrame.
          destruct draining.
          {
            destruct cap. all: try done.
            iFrame.
          }
          {
            iFrame.
          }

        }
        done.
      }
      {
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        assert ( sint.Z slice_val.(slice.len_f) = sint.Z (W64 0)).
        {
          destruct (sint.Z slice_val.(slice.len_f)). all: try done.
        }
        replace (sint.nat slice_val.(slice.len_f)) with 0%nat in *.
        { done.  }
        word.
      }
    }
Qed.

End atomic_specs.
