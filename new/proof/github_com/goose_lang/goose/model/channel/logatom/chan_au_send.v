From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.

From Perennial.algebra Require Import ghost_var.

#[local] Transparent is_channel own_channel.

Section atomic_specs.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Lemma wp_NewChannel (cap: Z) {B: BoundedTypeSize t} :
  0 ≤ cap < 2^63 ->
  {{{ True }}}
    channel.NewChannelⁱᵐᵖˡ #t #(W64 cap)
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_channel ch cap γ ∗
      own_channel ch cap (if decide (cap = 0) then chan_rep.Idle else chan_rep.Buffered []) γ
  }}}.
Proof.
  intros Hcap.
  wp_start. wp_call. wp_auto.
  wp_if_destruct.
  {
    assert (cap > 0) by word.
    rewrite -wp_fupd.
    wp_alloc mu as "mu".
    wp_auto.
    wp_apply (wp_slice_make2 (V:=V)); first done.
    iIntros (sl) ("Hsl"). wp_auto.
    wp_alloc ch as "Hch".
    wp_auto.
    rewrite /named.
    iDestruct (struct_fields_split with "Hch") as "Hch".
    iNamed "Hch". simpl.
    iMod (ghost_var_alloc (chan_rep.Buffered []))
      as (state_gname) "[Hstate_auth Hstate_frag]".
    iMod (ghost_var_alloc (None : option (offer_lock V)))
      as (offer_lock_gname) "Hoffer_lock".
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_parked_prop_gname) "Hparked_prop".
    {
      done.
    }
    iMod (saved_prop.saved_pred_alloc (K (λ (_ : V) (_ : bool),True%I))  (DfracOwn 1))
      as (offer_parked_pred_gname) "Hparked_pred";first done.
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_continuation_gname) "Hcontinuation";first done.
    set (γ := {|
               state_name := state_gname;
               offer_lock_name := offer_lock_gname;
               offer_parked_prop_name := offer_parked_prop_gname;
               offer_parked_pred_name := offer_parked_pred_gname;
               offer_continuation_name := offer_continuation_gname;
             |}).
    iPersist "Hcap Hmu".
    iMod ((init_lock (chan_inv_inner ch cap γ )) with "[$mu] [-HΦ Hstate_frag]") as "H".
    {
      iModIntro. unfold chan_inv_inner.
      iDestruct "Hsl" as "[Hsl Hos]".

      iExists (Buffered []). simpl.
      iFrame "#". iFrame.

      iPureIntro.
      unfold chan_cap_valid.
      lia.

    }
    iModIntro.  iApply "HΦ".
    iFrame "#". simpl.
    rewrite decide_False; [ | word ].
    iFrame. iPureIntro. unfold chan_cap_valid. lia.
  }
  {
    assert (cap = 0) by word; subst.

    rewrite -wp_fupd.
    wp_alloc mu as "mu".
    wp_auto.
    wp_apply (wp_slice_make2 (V:=V)); first done.
    iIntros (sl) ("Hsl"). wp_auto.
    wp_alloc ch as "Hch".
    wp_auto.
    rewrite /named.
    iDestruct (struct_fields_split with "Hch") as "Hch".
    iNamed "Hch". simpl.
    iMod (ghost_var_alloc chan_rep.Idle)
      as (state_gname) "[Hstate_auth Hstate_frag]".
    iMod (ghost_var_alloc (None : option (offer_lock V)))
      as (offer_lock_gname) "Hoffer_lock".
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_parked_prop_gname) "Hparked_prop".
    {
      done.
    }
    iMod (saved_prop.saved_pred_alloc (K (λ (_ : V) (_ : bool),True%I))  (DfracOwn 1))
      as (offer_parked_pred_gname) "Hparked_pred";first done.
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_continuation_gname) "Hcontinuation";first done.
    set (γ := {|
               state_name := state_gname;
               offer_lock_name := offer_lock_gname;
               offer_parked_prop_name := offer_parked_prop_gname;
               offer_parked_pred_name := offer_parked_pred_gname;
               offer_continuation_name := offer_continuation_gname;
             |}).
    iPersist "Hmu Hcap".
    iMod ((init_lock (chan_inv_inner ch 0 γ )) with "[$mu] [-HΦ Hstate_frag]") as "H".
    {
      iModIntro. unfold chan_inv_inner.
      iDestruct "Hsl" as "[Hsl Hos]".
      iExists (Idle).   simpl.
      iFrame "#". iFrame.
      iPureIntro.
      rewrite /chan_cap_valid //.
    }
    iModIntro.  iApply "HΦ".
    iFrame "#". simpl.
    iFrame.  iPureIntro. rewrite /chan_cap_valid //.
  }
Qed.

Lemma wp_Cap (ch: loc) (cap: Z) (γ: chan_names) :
  {{{ is_channel ch cap γ }}}
    channel.Channel__Capⁱᵐᵖˡ #ch #t #()
  {{{ RET #(W64 cap); True }}}.
Proof.
  wp_start as "#Hch". wp_call.
  wp_auto.
  iDestruct (is_channel_not_null with "Hch") as %Hnn.
  iNamed "Hch".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Len (ch: loc) (cap: Z) (γ: chan_names) :
  {{{ is_channel ch cap γ }}}
    channel.Channel__Lenⁱᵐᵖˡ #ch #t #()
  {{{ (l: w64), RET #l; ⌜0 ≤ sint.Z l ≤ cap⌝ }}}.
Proof.
  wp_start as "#His". wp_call.
  wp_auto.
  iDestruct (is_channel_not_null with "His") as %Hnn.
  iNamed "His".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  wp_call.
  wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  destruct s.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (Buffered buff); iFrame. }
    iApply "HΦ".
    iPureIntro.
    admit. (* TODO: does not seem tracked *)
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. iExists Idle; iFrame "∗#". }
    iApply "HΦ".
    iPureIntro.
    admit. (* need 0 ≤ cap *)
Admitted.

Lemma wp_TrySend (ch: loc) (cap: Z) (v: V) (γ: chan_names) (P: iProp Σ):
  ∀ Φ,
  is_channel ch cap γ -∗
  P ∗ (P -∗ ((send_au_slow ch cap v γ (Φ (#true))))) -∗
  (P -∗ (Φ (#false))) -∗
  WP channel.Channel__TrySendⁱᵐᵖˡ #ch #t #v #true {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "[HP HPau]". iIntros "HPfail".
  wp_call.
  iNamed "Hunb".
  wp_auto_lc 5.
  wp_call.
  wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s.

  - (* Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      wp_apply (wp_slice_append with "[$slice $Hsl $slice_cap]").
      iIntros (fr) "(Hfr & Hfrsl & Hsl)". wp_auto_lc 1.
      iApply "HPau" in "HP".
      unfold send_au_slow.

      iApply fupd_wp. iMod "HP".
      iMod (lc_fupd_elim_later with "[$] HP") as "Hlogatom".
      iNamed "Hlogatom".
      iAssert (own_channel ch cap (chan_rep.Buffered buff) γ)%I with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hown] [$Hoc]") as "%Hseq".
      subst s.

      iDestruct (own_channel_halves_update _ _ _ _ (chan_rep.Buffered (buff ++ [v]))
        with "[$Hoc] [$Hown]") as ">[Hgv1 Hgv2]".
      { done. }
      destruct (decide (length buff < cap)).
      {
        iMod ("Hcont" with "Hgv1") as "Hstep". iModIntro.
        wp_call.
        wp_apply (wp_lock_unlock with "[$lock state buffer Hfr Hfrsl Hgv2 $Hlock]").
        { unfold chan_inv_inner. iExists (Buffered (buff ++ [v])). iFrame. }
        done.
      }
      {
        replace (sint.Z slice_val.(slice.len_f)) with (sint.Z (length buff)) in * by word.
        word.
      }
    }
    {
      wp_call.
      wp_apply (wp_lock_unlock
        with "[$lock state slice_cap Hchanrepfrag buffer slice $Hlock]").
      { unfold chan_inv_inner. iExists (Buffered buff). iFrame.
        iPureIntro. done.
      }
      iApply "HPfail" in "HP". done.
    }
  - (* Idle - make offer *)
    iNamed "phys". wp_auto_lc 5.
    iNamed "offer".
    iDestruct ((offer_idle_to_send γ v P (Φ (# true))) with "Hoffer") as ">[offer1 offer2]".

    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer1 Hpred Hchanrepfrag HPau HP $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v). iFrame. iPureIntro. done. }

    wp_call.
    wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan".
    iNamed "phys". iNamed "offer".
    destruct s.

    + iNamed "phys". wp_auto_lc 5.
      unfold chan_cap_valid in Hcapvalid. subst cap.
      iNamed "offer".
      unfold chan_cap_valid in Hcapvalid. done.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      unfold offer_bundle_empty.
      iExFalso.
      iApply (saved_offer_half_full_invalid with "offer2 Hoffer").

    + unfold chan_phys. iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iDestruct ((offer_bundle_lc_agree γ (Some (chan_au_base.Snd v)) P (Φ (# true))
        (Some (chan_au_base.Snd v1)) P0 Φ0)
        with " [$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      iMod ((saved_prop.saved_pred_update (K Φr0)) with "Hpred") as "[Hpred1 Hpred2]".
      iCombine "Hpred1 Hpred2" as "Hp".
      wp_call.
      wp_apply (wp_lock_unlock
        with "[$lock state v slice slice_cap buffer Hchanrepfrag Hp H1 $Hlock]").
      { unfold chan_inv_inner. iExists (Idle). iFrame.
        iExists Φr0. iFrame. unfold saved_prop.saved_pred_own. rewrite dfrac_op_own Qp.half_half.
        iFrame.
        done.
      }
      iRewrite -"Hpeq" in "HP".
      iApply "HPfail" in "HP".
      done.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      discriminate Heq.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      discriminate Heq.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".

      unfold send_au_inner.
      iApply fupd_wp.
      iMod "Hau".
      iMod (lc_fupd_elim_later with "[$] Hau") as "HP".
      iNamed "HP".
      iAssert (own_channel ch cap (chan_rep.RcvCommit) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Hseq". subst s.
      iDestruct (own_channel_halves_update ch cap _ _
        (chan_rep.Idle)
        with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
      { done. }
      iMod ("Hcontinner" with "Hgv1") as "Hcont".
      iModIntro.
      iDestruct ((offer_bundle_lc_agree γ (Some (chan_au_base.Snd v)) P (Φ (# true))
        (Some (chan_au_base.Snd v1))
        P0 Φ0)
        with " [$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".

      wp_call.
      wp_apply (wp_lock_unlock
        with "[$lock state v slice slice_cap buffer Hpred Hgv2 Hpeq H1 $Hlock]").
      { unfold chan_inv_inner. iExists (Idle). iFrame. }
      unfold K.
      iRewrite -"H" in "Hcont". done.

    + iNamed "phys".
      unfold chan_logical.
      destruct draining.
      {
        iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
        iNamed "Hoc".
        unfold chan_cap_valid in *. subst cap. simpl.
        iNamed "Hoffer". unfold offer_bundle_empty.
        iDestruct (saved_offer_fractional_invalid with "[$offer2] [$Hoffer]") as "H".
        { done. }
        done.
      }
      {
        iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
        iNamed "Hoc".
        unfold chan_cap_valid in *. subst cap. iNamed "Hoffer". done.
      }

  - (* SndWait *)
    iNamed "phys". wp_auto_lc 5.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v0). iFrame. }
    iApply "HPfail" in "HP".
    done.

  - (* RcvWait - unbuffered channel *)
    iNamed "phys". wp_auto_lc 2.
    iNamed "offer". iDestruct "HP" as "HP0". iNamed "offer".
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
    iDestruct (own_channel_halves_update ch cap _ _ (chan_rep.RcvPending)
      with "[$Hown] [$Hown1]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont1". iModIntro.
    iApply "HPau" in "HP0".
    iApply fupd_wp.
    iMod (lc_fupd_elim_later with "[$] HP0") as "HP0".
    unfold rcv_au_fast.
    iMod "HP0".
    iMod (lc_fupd_elim_later with "[$] HP0") as "HP".
    iNamed "HP".
    iDestruct (own_channel_agree with "[$Hgv1] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update _ _ _ _ (chan_rep.SndCommit v)
      with "[$Hgv1] [$Hoc]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont". iModIntro.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer Hgv1 H2 Hpred Hoffer Hcont1 $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v). iFrame. iNamed "Hgv1". iFrame. }
    done.

  - (* SndDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v0). iFrame. }
    iApply "HPfail" in "HP". done.

  - (* RcvDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v0). iFrame. }
    iApply "HPfail" in "HP". done.

  - (* Closed *)
    destruct draining.
    {
      iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
      iNamed "Hoc". iApply "HPau" in "HP".
      unfold send_au_slow.
      iApply fupd_wp.
      iMod "HP".
      iMod (lc_fupd_elim_later with "[$] HP") as "HP".
      iNamed "HP".
      iAssert (own_channel ch cap (chan_rep.Closed []) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. }
      iDestruct (own_channel_agree with "[$Hoc] [$Hown]") as "%Hseq". subst s.
      done.
    }
    {
      iNamed "phys". iDestruct "offer" as "[Hoc %Hoffer]".
      iNamed "Hoc". iApply "HPau" in "HP".
      unfold send_au_slow.
      iApply fupd_wp.
      iMod "HP".
      iMod (lc_fupd_elim_later with "[$] HP") as "HP".
      iNamed "HP".
      iAssert (own_channel ch cap (chan_rep.Closed (v0 :: draining)) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hoc] [$Hown]") as "%Hseq". subst s.
      done.
    }
Qed.

Lemma wp_TrySend_nb (ch: loc) (cap: Z) (v: V) (γ: chan_names) (P: iProp Σ):
  ∀ Φ,
  is_channel ch cap γ -∗
  P ∗ (P -∗ ((send_au_fast ch cap v γ (Φ (#true))))) -∗
  (P -∗ (Φ (#false))) -∗
  WP channel.Channel__TrySendⁱᵐᵖˡ #ch #t #v #false {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "[HP HPau]". iIntros "HPfail".
  wp_call.
  iNamed "Hunb".
  wp_auto_lc 5.
  wp_call.
  wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s.

  { (* Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      wp_apply (wp_slice_append with "[$slice $Hsl $slice_cap]").
      iIntros (fr) "(Hfr & Hfrsl & Hsl)". wp_auto_lc 1.
      iApply "HPau" in "HP".
      unfold send_au_slow.

      iApply fupd_wp. iMod "HP".
      iMod (lc_fupd_elim_later with "[$] HP") as "Hlogatom".
      iNamed "Hlogatom".
      iAssert (own_channel ch cap (chan_rep.Buffered buff) γ)%I with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hown] [$Hoc]") as "%Hseq".
      subst s.

      iDestruct (own_channel_halves_update _ _ _ _ (chan_rep.Buffered (buff ++ [v]))
        with "[$Hoc] [$Hown]") as ">[Hgv1 Hgv2]".
      { done. }
      destruct (decide (length buff < cap)).
      {
        iMod ("Hcont" with "Hgv1") as "Hstep". iModIntro.
        wp_call.
        wp_apply (wp_lock_unlock with "[$lock state buffer Hfr Hfrsl Hgv2 $Hlock]").
        { unfold chan_inv_inner. iExists (Buffered (buff ++ [v])). iFrame. }
        done.
      }
      {
        replace (sint.Z slice_val.(slice.len_f)) with (sint.Z (length buff)) in * by word.
        word.
      }
    }
    {
      wp_call.
      wp_apply (wp_lock_unlock
        with "[$lock state slice_cap Hchanrepfrag buffer slice $Hlock]").
      { unfold chan_inv_inner. iExists (Buffered buff). iFrame.
        iPureIntro. done.
      }
      iApply "HPfail" in "HP". done.
    }
  }

  { (* Idle *)
    iNamed "phys". wp_auto_lc 5.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer HPau $Hlock]").
    { iFrame. unfold chan_inv_inner. iExists (Idle). iFrame. }
    iApply "HPfail" in "HP". done.
  }

  { (* SndWait *)
    iNamed "phys". wp_auto_lc 5.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v0). iFrame. }
    iApply "HPfail" in "HP".
    done.
  }

  { (* RcvWait - unbuffered channel *)
    iNamed "phys". wp_auto_lc 2.
    iNamed "offer". iDestruct "HP" as "HP0". iNamed "offer".
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
    iDestruct (own_channel_halves_update ch cap _ _ (chan_rep.RcvPending)
      with "[$Hown] [$Hown1]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont1". iModIntro.
    iApply "HPau" in "HP0".
    iApply fupd_wp.
    iMod (lc_fupd_elim_later with "[$] HP0") as "HP0".
    unfold rcv_au_fast.
    iMod "HP0".
    iMod (lc_fupd_elim_later with "[$] HP0") as "HP".
    iNamed "HP".
    iDestruct (own_channel_agree with "[$Hgv1] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update _ _ _ _ (chan_rep.SndCommit v)
      with "[$Hgv1] [$Hoc]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont". iModIntro.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer Hgv1 H2 Hpred Hoffer Hcont1 $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v). iFrame. iNamed "Hgv1". iFrame. }
    done.
  }

  { (* SndDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v0). iFrame. }
    iApply "HPfail" in "HP". done.
  }

  { (* RcvDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_call.
    wp_apply (wp_lock_unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v0). iFrame. }
    iApply "HPfail" in "HP". done.
  }

  { (* Closed *)
    destruct draining.
    {
      iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
      iNamed "Hoc". iApply "HPau" in "HP".
      unfold send_au_slow.
      iApply fupd_wp.
      iMod "HP".
      iMod (lc_fupd_elim_later with "[$] HP") as "HP".
      iNamed "HP".
      iAssert (own_channel ch cap (chan_rep.Closed []) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. }
      iDestruct (own_channel_agree with "[$Hoc] [$Hown]") as "%Hseq". subst s.
      done.
    }
    {
      iNamed "phys". iDestruct "offer" as "[Hoc %Hoffer]".
      iNamed "Hoc". iApply "HPau" in "HP".
      unfold send_au_slow.
      iApply fupd_wp.
      iMod "HP".
      iMod (lc_fupd_elim_later with "[$] HP") as "HP".
      iNamed "HP".
      iAssert (own_channel ch cap (chan_rep.Closed (v0 :: draining)) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame. iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hoc] [$Hown]") as "%Hseq". subst s.
      done.
    }
  }
Qed.

Lemma wp_Send (ch: loc) (cap: Z) (v: V) (γ: chan_names):
  ∀ Φ,
  is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au_slow ch cap v γ (Φ #())) -∗
  WP channel.Channel__Sendⁱᵐᵖˡ #ch #t #v {{ Φ }}.
Proof.
  intros. iIntros "#Hic". iIntros "Hau".
  iDestruct (is_channel_not_null with "[$Hic]") as "%Hnn".
  wp_call_lc "?".
  wp_auto_lc 3.
  iSpecialize ("Hau" with "[$]").

  wp_if_destruct; first done.
  wp_for. iNamed "Hau".
  wp_apply ((wp_TrySend ch cap v γ
    (send_au_slow ch cap v γ (Φ (# ())) ∗ c_ptr ↦ ch ∗ v_ptr ↦ v)%I)
    with "[$] [Hau c v]").
  { iFrame.
    iIntros "(Hau & c & v)".
    unfold send_au_slow. iMod "Hau".
    iModIntro. iModIntro. iNamed "Hau". iFrame.
    destruct s. all: try done.
    {
      destruct (decide (length buff < cap)).
      {
        iIntros "H". iMod ("Hcont" with "H") as "H".
        iModIntro. wp_auto. destruct decide.
        { wp_auto. wp_for_post. iFrame. naive_solver. }
        { destruct decide. { wp_auto. done. } done. }
      }
      { done. }
    }
    {
      iIntros "H". iMod ("Hcont" with "H") as "H".
      iModIntro. unfold send_au_inner. iMod "H". iModIntro. iModIntro.
      iNamed "H".
      iFrame.
      destruct s. all: try done.
      {
        iIntros "Hcontineer".
        iMod ("Hcontinner" with "Hcontineer") as "H". iModIntro. wp_auto.
        destruct decide. all:try naive_solver.
        destruct decide. all: try done.
        wp_auto. done.
      }
    }
    {
      iIntros "Hcontineer".
      iMod ("Hcont" with "Hcontineer") as "H". iModIntro. wp_auto.
      destruct decide. all:try naive_solver.
      destruct decide. all: try done. wp_auto.
      done.
    }
  }
  {
    iIntros "(Hau & c & v)". wp_auto.
    rewrite decide_True //.
    wp_auto. wp_for_post. iFrame.
  }
Qed.

Lemma wp_tryClose (ch: loc) (cap: Z) (γ: chan_names) (P: iProp Σ) :
  ∀ Φ,
  is_channel ch cap γ -∗
  P ∗ (P -∗ close_au ch cap γ (Φ (#true))) -∗
  (P -∗ (Φ (#false))) -∗
  WP channel.Channel__tryCloseⁱᵐᵖˡ #ch #t #() {{ Φ }}.
Proof.
  intros. iIntros "#Hunb". iIntros "[HP HPau]". iIntros "HPfail".
  wp_call.
  iNamed "Hunb".
  wp_auto_lc 1.

  (* Lock the channel *)
  wp_call.
  wp_apply (wp_lock_lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Open the atomic update *)
  unfold close_au.

  (* Case analysis on channel state *)
  destruct s; iNamed "phys".

  { (* Buffered *)
    iNamed "offer".
    iAssert (own_channel ch cap (chan_rep.Buffered buff) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame. iPureIntro. done. }
    wp_auto.
    iApply fupd_wp. iMod ("HPau" with "HP") as "Hau".
    iMod (lc_fupd_elim_later with "[$] Hau") as "Hau".
    iNamed "Hau".
    iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Heq".
    subst s.

    iDestruct (own_channel_halves_update _ _ _ _ (chan_rep.Closed buff)
      with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
    { move: Hcapvalid; rewrite /chan_cap_valid.
      destruct buff; auto. }
    iMod ("Hcontinner" with "Hgv1") as "HΦ".
    iModIntro.

    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state buffer slice slice_cap Hgv2 $Hlock]").
    { unfold chan_inv_inner.
      iExists (Closed buff). unfold chan_phys.
      destruct buff.
      { iFrame. destruct cap. all: try iFrame.
        { simpl. done. }
        { simpl. done. }
        { simpl. done. }
      }
      { iFrame. }
    }
    { iFrame. }
  }

  { (* Idle *)
    iNamed "offer".
    iApply fupd_wp.
    iMod ("HPau" with "HP") as "Hau".
    iMod (lc_fupd_elim_later with "[$] Hau") as "Hau".
    iNamed "Hau".
    iAssert (own_channel ch cap (chan_rep.Idle) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame. iPureIntro. done. }
    iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Heq".
    subst s.

    iDestruct (own_channel_halves_update _ _ _ _ (chan_rep.Closed [])
      with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcontinner" with "Hgv1") as "HΦ".
    iModIntro.

    wp_auto.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state v buffer slice slice_cap Hgv2 Hoffer $Hlock]").
    { unfold chan_inv_inner.
      iExists (Closed []). iFrame. destruct cap.
      { done. }
      { done. }
      { done. }
    }
    done.
  }

  { (* SndWait - can't close yet *)
    wp_auto.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v). iFrame. }
    iApply "HPfail" in "HP". iFrame.
  }

  { (* RcvWait - can't close yet *)
    wp_auto.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvWait). iFrame. }
    iApply "HPfail" in "HP". iFrame.
  }

  { (* SndDone - can't close yet *)
    wp_auto.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v). iFrame. }
    iApply "HPfail" in "HP". iFrame.
  }

  { (* RcvDone - can't close yet *)
    wp_auto.
    wp_call.
    wp_apply (wp_lock_unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v). iFrame. }
    iApply "HPfail" in "HP". iFrame.
  }

  { (* Closed - panic case *)
    iNamed "offer". unfold chan_logical.
    destruct draining.
    {
      iDestruct "offer" as "[offer1 offer2]".
      iApply fupd_wp.
      iMod ("HPau" with "HP") as "Hau".
      iMod (lc_fupd_elim_later with "[$] Hau") as "Hlogatom".
      iNamed "Hlogatom".
      iDestruct (own_channel_agree with "[$Hocinner] [$offer1]") as "%Heq".
      subst s.
      done.
    }
    {
      iDestruct "offer" as "[offer1 %offer2]".
      iApply fupd_wp.
      iMod ("HPau" with "HP") as "Hau".
      iMod (lc_fupd_elim_later with "[$] Hau") as "Hlogatom".
      iNamed "Hlogatom".
      iDestruct (own_channel_agree with "[$Hocinner] [$offer1]") as "%Heq".
      { iPureIntro. unfold chan_cap_valid. done. }
      subst s. done.
    }
  }
Qed.

Lemma wp_Close (ch: loc) (cap: Z) (γ: chan_names) :
  ∀ Φ,
  is_channel ch cap γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au ch cap γ (Φ #())) -∗
  WP channel.Channel__Closeⁱᵐᵖˡ #ch #t #() {{ Φ }}.
Proof.
  intros. iIntros "#Hic". iIntros "Hau".
  iDestruct (is_channel_not_null with "[$Hic]") as "%Hnn".
  wp_call_lc "?".
  wp_auto_lc 3.
  iSpecialize ("Hau" with "[$]").
  wp_if_destruct; first done.
  wp_for.

  wp_apply ((wp_tryClose ch cap γ (close_au ch cap γ (Φ (# ())) ∗ c_ptr ↦ ch)%I)
    with "[$Hic] [Hau c] []").
  { iFrame. iIntros "[Hau c]".
    unfold close_au. iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
    destruct s. all: try iFrame.
    {
      iIntros "H".
      iMod ("Hcontinner" with "H") as "H".
      iModIntro. wp_auto. destruct decide.
      {
        wp_auto. wp_for_post. naive_solver.
      }
      {
        destruct decide. all: try done. wp_auto. done.
      }
    }
    {
      iIntros "H".
      iMod ("Hcontinner" with "H") as "H".
      iModIntro. wp_auto. destruct decide.
      {
        wp_auto. wp_for_post. naive_solver.
      }
      {
        destruct decide. all: try done. wp_auto. done.
      }
    }
  }
  iIntros "Hau". iDestruct "Hau" as "[H1 H2]".
  iApply wp_fupd.
  wp_auto.
  destruct decide.
  { iModIntro. wp_auto. wp_for_post. iFrame. }
  done.
Qed.

End atomic_specs.
