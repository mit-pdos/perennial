From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
Require Import New.proof.github_com.goose_lang.primitive.

From Perennial.algebra Require Import ghost_var.

#[local] Transparent is_channel own_channel.
#[local] Typeclasses Transparent is_channel own_channel.

Section atomic_specs.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
(* FIXME: bundling? *)
Context {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics} {slice_sem : go.SliceSemantics}.

Context {package_sem : channel.Assumptions}.
Local Set Default Proof Using "All".

Context `[!chanG Σ V].
Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t] `[!go.TypeRepr t V].

Lemma wp_NewChannel (cap : w64) :
  {{{ ⌜ 0 ≤ sint.Z cap ⌝ }}}
    #(functions channel.NewChannel [t]) #cap
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_channel ch γ ∗
      ⌜chan_cap γ = sint.Z cap⌝ ∗
      own_channel ch (if decide (cap = W64 0) then chan_rep.Idle else chan_rep.Buffered []) γ
  }}}.
Proof.
  wp_start as "%Hle".
  wp_auto.
  wp_if_destruct.
  {
    wp_alloc mu as "mu".
    assert (sint.Z cap > 0) by word.
    rewrite -wp_fupd.
    wp_auto.
    wp_bind.
    wp_apply wp_slice_make2; first done.
    iIntros (sl) ("Hsl"). wp_auto.
    wp_alloc ch as "Hch".
    wp_auto.
    iStructNamedPrefix "Hch" "H".
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
               chan_cap := cap;
             |}).
    iPersist "Hcap Hmu".
    iMod ((init_lock (chan_inv_inner ch γ )) with "[$mu] [-HΦ Hstate_frag]") as "H".
    {
      iModIntro. unfold chan_inv_inner.
      iDestruct "Hsl" as "[Hsl Hos]".

      iExists (Buffered []). simpl.
      iFrame "#∗".

      iPureIntro.
      unfold chan_cap_valid.
      simpl. lia.

    }
    iModIntro. iApply ("HΦ" $! _ γ).
    iFrame "#". simpl.
    rewrite decide_False; [ | word ].
    unfold is_channel. iFrame "∗#". iPureIntro.
    assert (ch ≠ chan.nil) by admit. (* FIXME: non-nilness. *)
    split; first done. unfold chan_cap_valid. simpl; word.
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
    iStructNamedPrefix "Hch" "H". simpl.
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
               chan_cap := 0;
             |}).
    iPersist "Hmu Hcap".
    iMod ((init_lock (chan_inv_inner ch γ )) with "[$mu] [-HΦ Hstate_frag]") as "H".
    {
      iModIntro. unfold chan_inv_inner.
      iDestruct "Hsl" as "[Hsl Hos]".
      iExists (Idle).   simpl.
      iFrame "#". iFrame.
      iPureIntro.
      rewrite /chan_cap_valid //.
    }
    iModIntro.  iApply ("HΦ" $! _ γ).
    unfold is_channel. iFrame "∗#". simpl.
    iFrame "∗#". assert (ch ≠ chan.nil) by admit. (* FIXME: non-nilness. *)
    iPureIntro. rewrite /chan_cap_valid //.
  }
Admitted.

Lemma wp_Cap (ch: loc) (γ: chan_names) :
  {{{ is_channel ch γ }}}
    #(methods (go.PointerType (channel.Channel t)) "Cap") #ch #()
  {{{ RET #(chan_cap γ); True }}}.
Proof.
  wp_start as "#Hch". wp_auto.
  iDestruct (is_channel_not_null with "Hch") as %Hnn.
  iNamed "Hch".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Len (ch: loc) (γ: chan_names) :
  {{{ is_channel ch γ }}}
    #(methods (go.PointerType (channel.Channel t)) "Len") #ch #()
  {{{ (l: w64), RET #l; ⌜0 ≤ sint.Z l ≤ sint.Z $ chan_cap γ⌝ }}}.
Proof.
  wp_start as "#His".
  wp_auto.
  iDestruct (is_channel_not_null with "His") as %Hnn.
  iNamed "His".
  rewrite bool_decide_eq_false_2 //.
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  destruct s.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    cbn [chan_logical].
    iDestruct (own_channel_buffer_size with "offer") as %Heq.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (Buffered buff); iFrame. }
    iApply "HΦ".
    iPureIntro.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - iNamed "phys".
    wp_auto.
    iDestruct (own_slice_len with "slice") as %Hlen.
    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer v $Hlock]").
    { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
    iApply "HΦ".
    iPureIntro.
    simpl in *.
    word.
  - (* Closed(draining) *)
    destruct draining.
    {
      (* draining = nil *)
      iNamed "phys".
      wp_auto.
      iDestruct (own_slice_len with "slice") as %Hlen.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
      { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
      iApply "HΦ".
      iPureIntro.
      simpl in *.
      word.
    }
    (* length draining > 0 *)
    {
      iNamed "phys".
      iAssert (⌜1 + (Z.of_nat (length draining)) ≤ sint.Z $ chan_cap γ⌝)%I as %Hdraining_bound.
      {
        iNamedSuffix "offer" "2".
        simpl in Hcapvalid2.
        iPureIntro. lia.
      }
      wp_auto.
      iDestruct (own_slice_len with "slice") as %Hlen.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap offer $Hlock]").
      { unfold chan_inv_inner. rewrite /named. iFrame "offer ∗". }
      iApply "HΦ".
      iPureIntro.
      simpl in *.
      lia.
    }
Qed.

Local Lemma wp_TrySend_blocking (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  send_au_slow ch v γ (Φ (#true)) ∧ Φ (#false) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "TrySend") #ch #v #true {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "HΦ".
  wp_method_call. wp_call. iNamed "Hunb".
  wp_auto_lc 5.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s.

  - (* Buffered channel *)
    iNamed "phys". iNamed "offer". wp_auto. unfold chan_cap_valid in Hcapvalid.
    wp_if_destruct.
    {
      iDestruct (slice_array with "tmp") as "Hsl"; first done.
      rewrite go.array_index_ref_0 /=.
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      wp_apply (wp_slice_append with "[$slice $Hsl $slice_cap]").
      iIntros (fr) "(Hfr & Hfrsl & Hsl)". wp_auto_lc 1.
      unfold send_au_slow.

      iApply fupd_wp. iLeft in "HΦ". iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "Hlogatom".
      iNamed "Hlogatom".
      iAssert (own_channel ch (chan_rep.Buffered buff) γ)%I with "[Hchanrepfrag]" as "Hown".
      { iFrame "#∗". iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hown] [$Hoc]") as "%Hseq".
      subst s.
      assert (length buff < sint.Z $ chan_cap γ).
      { word. }

      iDestruct (own_channel_halves_update (chan_rep.Buffered (buff ++ [v]))
        with "[$Hoc] [$Hown]") as ">[Hgv1 Hgv2]".
      { simpl. len. }
      iMod ("Hcont" with "Hgv1") as "Hstep". iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer Hfr Hfrsl Hgv2 $Hlock]").
      { unfold chan_inv_inner. iExists (Buffered (buff ++ [v])). iFrame. }
      done.
    }
    {
      wp_apply (wp_Mutex__Unlock
        with "[$lock state slice_cap Hchanrepfrag buffer slice $Hlock]").
      { unfold chan_inv_inner. iExists (Buffered buff). iFrame "#∗".
        iPureIntro. done.
      }
      iRight in "HΦ". iFrame.
    }
  - (* Idle - make offer *)
    iNamed "phys". wp_auto_lc 4.
    iNamed "offer".
    iDestruct (offer_idle_to_send γ v (_ ∧ Φ #false) (Φ (# true)) with "Hoffer") as ">[offer1 offer2]".

    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer1 Hpred Hchanrepfrag HΦ $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v). iFrame. iSplitL; last done.
      iIntros "H". iLeft in "H". iFrame. }

    wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan".
    iNamed "phys". iNamed "offer".
    destruct s.

    + iNamed "phys". wp_auto_lc 5.
      simpl in Hcapvalid.
      iNamedSuffix "offer" "2".
      simpl in Hcapvalid2.
      lia.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      unfold offer_bundle_empty.
      iExFalso.
      iApply (saved_offer_half_full_invalid with "offer2 Hoffer").

    + unfold chan_phys. iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iDestruct (offer_bundle_lc_agree with "[$] [$offer2] [$Hoffer]") as ">(%Heq & Hpeq & H & H1)".
      iMod (saved_prop.saved_pred_update (K Φr0) with "Hpred") as "[Hpred1 Hpred2]".
      iCombine "Hpred1 Hpred2" as "Hp".
      wp_apply (wp_Mutex__Unlock
        with "[$lock state v slice slice_cap buffer Hchanrepfrag Hp H1 $Hlock]").
      { unfold chan_inv_inner. iExists (Idle). iFrame.
        iExists Φr0. iFrame. unfold saved_prop.saved_pred_own. rewrite dfrac_op_own Qp.half_half.
        iFrame "∗#".
        done.
      }
      iRewrite -"Hpeq" in "HP".
      iRight in "HP". iFrame.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      congruence.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".
      iExFalso.
      iDestruct (offer_bundle_agree with "[$offer2 $Hoffer]") as "[%Heq _]".
      congruence.

    + iNamed "phys". wp_auto_lc 5.
      iNamed "offer".

      unfold send_au_inner.
      iApply fupd_wp.
      iMod "Hau".
      iMod (lc_fupd_elim_later with "[$] Hau") as "HP".
      iNamed "HP".
      iAssert (own_channel ch (chan_rep.RcvCommit) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Hseq". subst s.
      iDestruct (own_channel_halves_update (chan_rep.Idle)
        with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
      { done. }
      iMod ("Hcontinner" with "Hgv1") as "Hcont".
      iModIntro.
      iDestruct (offer_bundle_lc_agree with "[$] [$offer2] [$Hoffer]") as
        ">(%Heq & Hpeq & H & H1)".
      wp_apply (wp_Mutex__Unlock
        with "[$lock state v slice slice_cap buffer Hpred Hgv2 Hpeq H1 $Hlock]").
      { unfold chan_inv_inner. iExists (Idle). iFrame. }
      unfold K.
      iRewrite -"H" in "Hcont". done.

    + iNamed "phys".
      unfold chan_logical.
      destruct draining.
      {
        iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
        iNamedSuffix "Hoc" "2".
        unfold chan_cap_valid in *.
        iNamed "Hoffer". iSpecialize ("Hoffer" with "[%]"); first word. unfold offer_bundle_empty.
        iDestruct (saved_offer_fractional_invalid with "[$offer2] [$Hoffer]") as "H".
        { done. }
        done.
      }
      {
        iNamed "phys". iNamedSuffix "offer" "2".
        cbn [chan_cap_valid] in *.
        lia.
      }

  - (* SndWait *)
    iNamed "phys". wp_auto_lc 5.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v0). iFrame. }
    iRight in "HΦ". iApply "HΦ".

  - (* RcvWait - unbuffered channel *)
    (* NOTE: this leaves no freedom for picking the linearization order. *)
    iNamed "phys". wp_auto_lc 2. iNamed "offer".
    iApply "Hau" in "HP".
    iApply fupd_wp. iMod "HP".
    iMod (lc_fupd_elim_later with "[$] HP") as "HP".
    iNamed "HP".
    iDestruct "Hoc" as "[H1 H2]".
    iDestruct (chan_rep_agree with "[$H1] [$Hchanrepfrag]") as "%Hseq". subst s.
    iAssert (own_channel ch (chan_rep.Idle) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iAssert (own_channel ch (chan_rep.Idle) γ)%I
      with "[H1]" as "Hown1".
    { iFrame. iPureIntro. done. }
    iDestruct (own_channel_halves_update (chan_rep.RcvPending) with "[$Hown] [$Hown1]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont1".
    iLeft in "HΦ". iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ".
    iDestruct (own_channel_agree with "[$Hgv1] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update (chan_rep.SndCommit _)
      with "[$Hgv1] [$Hoc]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcont" with "Hgv2") as "Hcont". iModIntro.
    iDestruct "Hgv1" as "[Hgv1 _]".
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer Hgv1 Hcont1 H2 Hpred Hoffer $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v).
      Opaque rcv_au_inner. iFrame. Transparent rcv_au_inner. }
    (* FIXME: either iFrame is doing something wrong or the invariant is
       improperly written. *)
    done.

  - (* SndDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v0). iFrame. }
    iRight in "HΦ". done.

  - (* RcvDone *)
    iNamed "phys". wp_auto_lc 2.
    wp_apply (wp_Mutex__Unlock
      with "[$lock state v slice slice_cap buffer offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v0). iFrame. }
    iRight in "HΦ". done.

  - (* Closed *)
    destruct draining.
    {
      iNamed "phys". iDestruct "offer" as "[Hoc Hoffer]".
      iNamed "Hoc". iLeft in "HΦ". iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iAssert (own_channel ch (chan_rep.Closed []) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#%". }
      iDestruct (own_channel_agree with "[$Hoc] [$Hown]") as "%Hseq". subst s.
      done.
    }
    {
      iNamed "phys". iDestruct "offer" as "[Hoc %Hoffer]".
      iNamed "Hoc". iLeft in "HΦ". iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iAssert (own_channel ch (chan_rep.Closed (v0 :: draining)) γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }
      iDestruct (own_channel_agree with "[$Hoc] [$Hown]") as "%Hseq". subst s.
      done.
    }
Qed.

Local Lemma wp_TrySend_nonblocking (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  send_au_fast ch v γ (Φ (#true)) (Φ (#false)) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "TrySend") #ch #v #false {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "HΦ". wp_method_call. wp_call.
  iNamed "Hunb". wp_auto_lc 5.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamedSuffix "Hchan" "_inv".

  (* Case analysis on channel state *)
  destruct s; iNamedSuffix "phys_inv" "_inv".
  - (* Buffered channel *)
    iNamedSuffix "offer_inv" "_inv".
    wp_auto. unfold chan_cap_valid in *.

    (* TODO: tactics to saturate the context with facts like these? *)
    iDestruct (own_slice_len with "[$]") as "%Hlen".
    iDestruct (own_slice_wf with "[$]") as "%Hwf".
    iDestruct (own_slice_cap_wf with "[$]") as "%Hwf2".

    wp_if_destruct.
    +
      iApply fupd_wp. iLeft in "HΦ". iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
      iDestruct (own_channel_halves_update (chan_rep.Buffered (buff ++ [v]))
        with "[$Hchanrepfrag] [$Hchanrepfrag_inv]") as ">[Hchanrepfrag Hchanrepfrag_inv]".
      { simpl in *. len. }
      { simpl in *. len. }
      { simpl in *. len. }
      iMod ("Hcont" with "Hchanrepfrag") as "Hstep". iModIntro.
      iDestruct (slice_array with "tmp") as "Hsl".
      { done. }
      rewrite go.array_index_ref_0.
      wp_apply (wp_slice_append with "[$slice_inv $Hsl $slice_cap_inv]").
      iIntros (fr) "(slice_inv & slice_cap_inv & Hsl)". wp_auto.
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (Buffered (buff ++ [v])). iFrame. }
      done.
    + iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock
        with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (Buffered buff). iFrame "∗#%". }
      iRight in "HΦ". done.
  - (* Idle *)
    wp_auto_lc 5.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
      with "[$lock $Hlock Hi]").
    { iNamed "Hi". iFrame. unfold chan_inv_inner. iExists (Idle). iFrame. }
    iRight in "HΦ". iFrame.
  - (* SndWait *)
    wp_auto_lc 5.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (SndWait v0). iFrame. }
    iRight in "HΦ". iFrame.
  - (* RcvWait - unbuffered channel *)
    wp_auto_lc 2. iNamedSuffix "offer_inv" "_inv".
    unfold send_au_slow.
    iApply fupd_wp. iApply "Hau_inv" in "HP_inv". iMod "HP_inv".
    iMod (lc_fupd_elim_later with "[$] HP_inv") as "HP_inv". iNamed "HP_inv".
    iNamed "Hoc".
    iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
    iDestruct (own_channel_halves_update (chan_rep.RcvPending)
      with "[$Hchanrepfrag] [$Hchanrepfrag_inv]") as ">[Hchanrepfrag Hchanrepfrag_inv]";
      [done..|].
    iMod ("Hcont" with "[$Hchanrepfrag]") as "Hcont1_inv". iModIntro.
    iLeft in "HΦ".
    iApply fupd_wp.
    iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HP".
    iNamed "HP".
    iDestruct (own_channel_agree with "[$Hchanrepfrag_inv] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update (chan_rep.SndCommit v)
      with "[$Hchanrepfrag_inv] [$Hoc]") as ">[Hoc Hchanrepfrag_inv]".
    { done. }
    iMod ("Hcont" with "Hoc") as "Hcont". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
      with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (SndDone v). iFrame "∗#". }
    done.
  - (* SndDone *)
    wp_auto_lc 2. iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
      with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (SndDone v0). iFrame. }
    iRight in "HΦ". iFrame.
  - (* RcvDone *)
    wp_auto_lc 2. iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
      with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (RcvDone v0). iFrame. }
    iRight in "HΦ". iFrame.
  - (* Closed *)
    destruct draining; iNamedSuffix "phys_inv" "_inv".
    + simpl. iDestruct "offer_inv" as "[Hoc_inv offer_inv]". iLeft in "HΦ".
      unfold send_au_slow.
      iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iDestruct (own_channel_agree with "Hoc Hoc_inv") as "%Hseq". subst s.
      done.
    + simpl. iDestruct "offer_inv" as "Hoc_inv".
      iLeft in "HΦ".
      unfold send_au_slow.
      iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iDestruct (own_channel_agree with "[$Hoc] [$Hoc_inv]") as "%Hseq". subst s.
      done.
Qed.

Local Lemma wp_TrySend_nonblocking_alt (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  send_au_fast_alt ch v γ (Φ (#true)) (Φ (#false)) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "TrySend") #ch #v #false {{ Φ }}.
Proof.
  intros. iIntros "Hunb". iIntros "HΦ". wp_method_call. wp_call.
  iNamed "Hunb". wp_auto.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamedSuffix "Hchan" "_inv".

  (* Case analysis on channel state *)
  destruct s; iNamedSuffix "phys_inv" "_inv".
  - (* Buffered channel *)
    iNamedSuffix "offer_inv" "_inv".
    wp_auto_lc 1. unfold chan_cap_valid in *.

    (* TODO: tactics to saturate the context with facts like these? *)
    iDestruct (own_slice_len with "[$]") as "%Hlen".
    iDestruct (own_slice_wf with "[$]") as "%Hwf".
    iDestruct (own_slice_cap_wf with "[$]") as "%Hwf2".

    wp_if_destruct.
    + iApply fupd_wp. iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
      iDestruct (own_channel_halves_update (chan_rep.Buffered (buff ++ [v]))
        with "[$Hchanrepfrag] [$Hchanrepfrag_inv]") as ">[Hchanrepfrag Hchanrepfrag_inv]";
        [ simpl in *; len .. | ].
      destruct decide.
      2:{ exfalso. word. }
      iMod ("Hcont" with "Hchanrepfrag") as "Hstep". iModIntro.
      iDestruct (slice_array with "tmp") as "Hsl"; first done.
      rewrite go.array_index_ref_0.
      wp_apply (wp_slice_append with "[$slice_inv $Hsl $slice_cap_inv]").
      iIntros (fr) "(slice_inv & slice_cap_inv & Hsl)". wp_auto.
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (Buffered (buff ++ [v])). iFrame. }
      done.
    + iApply fupd_wp. iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ". iNamed "Hoc".
      iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
      destruct decide.
      { exfalso. word. }
      iMod ("Hcont" with "[$Hchanrepfrag]") as "HΦ"; first done.
      iModIntro.
      iCombineNamed "*_inv" as "Hi".
      wp_apply (wp_Mutex__Unlock
        with "[$lock $Hlock Hi]").
      { iNamed "Hi". unfold chan_inv_inner. iExists (Buffered buff). iFrame "∗#%". }
      iFrame.
  - (* Idle *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp. iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ". iNamed "Hoc".
    iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
    iMod ("Hcont" with "[$Hchanrepfrag]") as "HΦ"; first done.
    iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists Idle. iFrame "∗#%". }
    iFrame.
  - (* SndWait *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp. iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ". iNamed "Hoc".
    iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
    iMod ("Hcont" with "[$Hchanrepfrag]") as "HΦ"; first done.
    iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (SndWait _). iFrame "∗#%". }
    iFrame.
  - (* RcvWait *)
    wp_auto_lc 2. iNamedSuffix "offer_inv" "_inv".
    unfold send_au_slow.
    iApply fupd_wp. iApply "Hau_inv" in "HP_inv". iMod "HP_inv".
    iMod (lc_fupd_elim_later with "[$] HP_inv") as "HP_inv". iNamed "HP_inv".
    iNamed "Hoc".
    iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
    iDestruct (own_channel_halves_update (chan_rep.RcvPending)
      with "[$Hchanrepfrag] [$Hchanrepfrag_inv]") as ">[Hchanrepfrag Hchanrepfrag_inv]";
      [done..|].
    iMod ("Hcont" with "[$Hchanrepfrag]") as "Hcont1_inv". iModIntro.
    iApply fupd_wp. iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HP".
    iNamed "HP".
    iDestruct (own_channel_agree with "[$Hchanrepfrag_inv] [$Hoc]") as "%Hseq". subst s.
    iDestruct (own_channel_halves_update (chan_rep.SndCommit v)
      with "[$Hchanrepfrag_inv] [$Hoc]") as ">[Hoc Hchanrepfrag_inv]".
    { done. }
    iMod ("Hcont" with "Hoc") as "Hcont". iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
      with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (SndDone v). iFrame "∗#". }
    done.
  - (* SndDone *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp. iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ". iNamed "Hoc".
    iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
    iMod ("Hcont" with "[$Hchanrepfrag]") as "HΦ"; first done.
    iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (SndDone _). iFrame "∗#%". }
    iFrame.
  - (* RcvDone *)
    wp_auto_lc 1.
    iNamedSuffix "offer_inv" "_inv".
    iApply fupd_wp. iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ". iNamed "Hoc".
    iCombine "Hchanrepfrag_inv Hchanrepfrag" gives %[_ Hseq]. subst.
    iMod ("Hcont" with "[$Hchanrepfrag]") as "HΦ"; first done.
    iModIntro.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock
               with "[$lock $Hlock Hi]").
    { iNamed "Hi". unfold chan_inv_inner. iExists (RcvDone _). iFrame "∗#%". }
    iFrame.
  - (* Closed *)
    destruct draining; iNamedSuffix "phys_inv" "_inv".
    + wp_auto_lc 1.
      simpl. iDestruct "offer_inv" as "[Hoc_inv offer_inv]".
      iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iDestruct (own_channel_agree with "Hoc Hoc_inv") as "%Hseq". subst s.
      done.
    + wp_auto_lc 1.
      simpl. iDestruct "offer_inv" as "Hoc_inv".
      iApply fupd_wp.
      iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
      iNamed "HΦ".
      iDestruct (own_channel_agree with "[$Hoc] [$Hoc_inv]") as "%Hseq". subst s.
      done.
Qed.

Lemma wp_TrySend (ch: loc) (v: V) (γ: chan_names) (blocking : bool) :
  ∀ Φ,
  is_channel ch γ -∗
  (if blocking then send_au_slow ch v γ (Φ (#true)) ∧ Φ (#false)
   else (send_au_fast ch v γ (Φ (#true)) (Φ (#false)) ∨ send_au_fast_alt ch v γ (Φ (#true)) (Φ (#false))))
  -∗
  WP #(methods (go.PointerType (channel.Channel t)) "TrySend") #ch #v #blocking {{ Φ }}.
Proof.
  iIntros (?) "#? HΦ".
  destruct blocking.
  - wp_apply (wp_TrySend_blocking with "[$] [$]").
  - iDestruct "HΦ" as "[?|?]".
    + wp_apply (wp_TrySend_nonblocking with "[$] [$]").
    + wp_apply (wp_TrySend_nonblocking_alt with "[$] [$]").
Qed.

Lemma wp_Send (ch: loc) (v: V) (γ: chan_names):
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ send_au_slow ch v γ (Φ #())) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "Send") #ch #v {{ Φ }}.
Proof.
  intros. iIntros "#Hic". iIntros "Hau".
  iDestruct (is_channel_not_null with "[$Hic]") as "%Hnn".
  wp_method_call. wp_call.
  wp_auto_lc 4.
  iSpecialize ("Hau" with "[$]").

  wp_if_destruct; first done.
  wp_for. iNamed "Hau".
  wp_apply (wp_TrySend with "[$] [Hau c v]").
  iSplit.
  { iFrame.
    unfold send_au_slow. iMod "Hau".
    iModIntro. iModIntro. iNamed "Hau". iFrame.
    destruct s. all: try done.
    {
      iIntros "H".
      iMod ("Hcont" with "H") as "H".
      iModIntro. wp_auto. destruct decide.
      { wp_auto. wp_for_post. iFrame. naive_solver. }
      destruct decide. { wp_auto. done. } done.
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
        destruct decide; try naive_solver.
        destruct decide; try done.
        wp_auto. done.
      }
    }
    {
      iIntros "Hcontineer".
      iMod ("Hcont" with "Hcontineer") as "H". iModIntro. wp_auto.
      destruct decide; try naive_solver.
      destruct decide; try done. wp_auto.
      done.
    }
  }
  {
    wp_auto.
    rewrite decide_True //.
    wp_auto. wp_for_post. iFrame.
  }
Qed.

(** Demo of a simple-to-understand AU *)
#[local] Lemma wp_BlockingSend (ch: loc) (v: V) (γ: chan_names):
  sint.Z γ.(chan_cap) > 0 →
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ buffered_send_au ch v γ (Φ #())) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "Send") #ch #v {{ Φ }}.
Proof.
  iIntros (Hcapnz Φ) "#Hunb HΦ".
  iApply (wp_Send with "[$Hunb]").
  iIntros "Hlc".
  iSpecialize ("HΦ" with "[$Hlc]").
  rewrite /send_au_slow /buffered_send_au.
  iMod "HΦ". iIntros "!> !>".
  iNamed "HΦ".
  destruct s; iFrame; auto.
  - iIntros "Hoc".
    iExFalso.
    iNamed "Hoc". simpl in *.
    lia.
  - iIntros "Hoc".
    iExFalso.
    iNamed "Hoc". simpl in *.
    lia.
Qed.

Local Lemma wp_tryClose (ch: loc) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  close_au ch γ (Φ (#true)) ∧ Φ (#false) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "tryClose") #ch #() {{ Φ }}.
Proof.
  intros. iIntros "#Hunb". iIntros "HΦ".
  wp_method_call. wp_call.
  iNamed "Hunb".
  wp_auto_lc 1.

  (* Lock the channel *)
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Open the atomic update *)
  unfold close_au.

  (* Case analysis on channel state *)
  destruct s; iNamed "phys".

  { (* Buffered *)
    iNamed "offer".
    iAssert (own_channel ch (chan_rep.Buffered buff) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    wp_auto.
    iApply fupd_wp. iLeft in "HΦ". iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ".
    iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Heq".
    subst s.

    iDestruct (own_channel_halves_update (chan_rep.Closed buff)
      with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
    { move: Hcapvalid; rewrite /chan_cap_valid.
      destruct buff; lia. }
    iMod ("Hcontinner" with "Hgv1") as "HΦ".
    iModIntro.

    wp_apply (wp_Mutex__Unlock with "[$lock state buffer slice slice_cap Hgv2 $Hlock]").
    { unfold chan_inv_inner.
      iExists (Closed buff). unfold chan_phys.
      destruct buff.
      { iFrame.
        iIntros "%Hcap0".
        exfalso; simpl in *; word.
      }
      { iFrame. }
    }
    { iFrame. }
  }

  { (* Idle *)
    iNamed "offer".
    iApply fupd_wp.
    iLeft in "HΦ". iMod "HΦ".
    iMod (lc_fupd_elim_later with "[$] HΦ") as "HΦ".
    iNamed "HΦ".
    iAssert (own_channel ch (chan_rep.Idle) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iFrame "∗#". iPureIntro. done. }
    iDestruct (own_channel_agree with "[$Hocinner] [$Hown]") as "%Heq".
    subst s.

    iDestruct (own_channel_halves_update (chan_rep.Closed [])
      with "[$Hocinner] [$Hown]") as ">[Hgv1 Hgv2]".
    { done. }
    iMod ("Hcontinner" with "Hgv1") as "HΦ".
    iModIntro.

    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap Hgv2 Hoffer $Hlock]").
    { unfold chan_inv_inner.
      iExists (Closed []). iFrame. iIntros "Hcap". done.
    }
    done.
  }

  { (* SndWait - can't close yet *)
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndWait v). iFrame. }
    iRight in "HΦ". iFrame.
  }

  { (* RcvWait - can't close yet *)
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvWait). iFrame. }
    iRight in "HΦ". iFrame.
  }

  { (* SndDone - can't close yet *)
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (SndDone v). iFrame. }
    iRight in "HΦ". iFrame.
  }

  { (* RcvDone - can't close yet *)
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$lock state v buffer slice slice_cap offer $Hlock]").
    { unfold chan_inv_inner. iExists (RcvDone v). iFrame. }
    iRight in "HΦ". iFrame.
  }

  { (* Closed - panic case *)
    iNamed "offer". unfold chan_logical.
    destruct draining.
    {
      iDestruct "offer" as "[offer1 offer2]".
      iApply fupd_wp.
      iLeft in "HΦ". iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "Hlogatom".
      iNamed "Hlogatom".
      iDestruct (own_channel_agree with "[$Hocinner] [$offer1]") as "%Heq".
      subst s.
      done.
    }
    {
      iDestruct "offer" as "(offer1 & %offer2)".
      iApply fupd_wp.
      iLeft in "HΦ". iMod "HΦ".
      iMod (lc_fupd_elim_later with "[$] HΦ") as "Hlogatom".
      iNamed "Hlogatom".
      iDestruct (own_channel_agree with "[$Hocinner] [$offer1]") as "%Heq".
      { iFrame "#". iPureIntro. unfold chan_cap_valid. done. }
      subst s. done.
    }
  }
Qed.

Lemma wp_Close (ch: loc) (γ: chan_names) :
  ∀ Φ,
  is_channel ch γ -∗
  (£1 ∗ £1 ∗ £1 ∗ £1 -∗ close_au ch γ (Φ #())) -∗
  WP #(methods (go.PointerType (channel.Channel t)) "Close") #ch #() {{ Φ }}.
Proof.
  intros. iIntros "#Hic". iIntros "Hau".
  iDestruct (is_channel_not_null with "[$Hic]") as "%Hnn".
  wp_method_call. wp_call.
  wp_auto_lc 4.
  iSpecialize ("Hau" with "[$]").
  wp_if_destruct; first done.
  wp_for.

  wp_apply (wp_tryClose with "[$Hic]").
  iSplit.
  { iFrame.
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
  {
    wp_auto. rewrite decide_True //. wp_auto.
    wp_for_post. iFrame.
  }
Qed.

End atomic_specs.
