From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base chan_init.
From New.proof Require Import proof_prelude.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.sync_proof Require Import mutex sema.

Section atomic_specs.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

(* Used for a standalone send as well as a send case in a blocking select statement. 
   This tracks the possible success paths for both unbuffered and buffered channels.
*)
Definition chan_blocking_send_atomic_update ch (cap: w64) (v : V) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
  "#Hperschan" ∷ is_channel ch cap γ ∗
  "Hlogatom" ∷ |={⊤,∅}=>
    ▷∃ s,  "Hoc" ∷ own_channel ch s cap γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Buffered channel with available capacity, enqueue the value. *)
    | chan_rep.Buffered buff =>
      if decide (length buff < uint.Z cap) then
        (* Space available: enqueue the value *)
        own_channel ch (chan_rep.Buffered (buff ++ [v])) cap γ ={∅,⊤}=∗ Φ
      else
        (* Buffer full: not applicable for blocking send when it succeeds *)
        |={∅, ⊤}=> True
    (* Case: Unbuffered channel with waiting receiver, complete the exchange. *)
    | chan_rep.RcvWait =>
          own_channel ch (chan_rep.SndDone v) 0 γ ={∅,⊤}=∗ Φ
    (* Case: Unbuffered idle channel. This requires a two-phase handshake. *)
    | chan_rep.Idle =>
          (* Register as a waiting sender *)
          own_channel ch (chan_rep.SndWait v) 0 γ ={∅,⊤}=∗
               |={⊤,∅}=> ▷∃ s', own_channel ch s' 0 γ ∗
                 (match s' with
                    (* If we succeed through this path, the receiver completed the offer *)
                    | chan_rep.RcvDone =>
                        own_channel ch chan_rep.Idle 0 γ ={∅,⊤}=∗ Φ
                  | chan_rep.Closed _ => False
                    | _ =>  |={∅, ⊤}=> True
                 end)
    | chan_rep.SndWait _ | chan_rep.RcvDone | chan_rep.SndDone _ =>  |={∅, ⊤}=>  True
    | chan_rep.Closed _ => False
    end).

(* Used for an attempt at sending that is part of a nonblocking select statement. *)
Definition chan_nonblocking_send_atomic_update ch (cap: w64) (v : V) (γ: chan_names) (Φsuccess : iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
   "#Hperschan" ∷ is_channel ch cap γ ∗
   "Hlogatom" ∷ |={⊤,∅}=>
    ▷∃ s,  "Hoc" ∷ own_channel ch s cap γ ∗
     "Hcont" ∷
    match s with
    (* Case: Buffered channel. If the buffer is full, the send fails. *)
    | chan_rep.Buffered buff =>
         if decide (length buff < uint.Z cap) then
           (* Success path: add to buffer *)
           (own_channel ch (chan_rep.Buffered (buff ++ [v])) cap γ ={∅,⊤}=∗ Φsuccess)
         else
           (* Buffer full, not selectable *)
           (own_channel ch s cap γ ={∅,⊤}=∗ Φnotready)
    (* Case: Unbuffered channel. Succeeds only if there's a waiting receiver. *)
    | chan_rep.RcvWait =>
         own_channel ch (chan_rep.SndDone v) cap γ ={∅,⊤}=∗ Φsuccess
    (* Case: Channel is closed. *)
    | chan_rep.Closed _ =>
         False (* Send on closed channel - should panic *)
    (* Case: Unbuffered channel without a waiting receiver. The send fails immediately. *)
    | _ =>
        own_channel ch s cap γ ={∅,⊤}=∗ Φnotready
    end.

(* This is used for the offer-based try loop used for blocking select statements.
   It should not be used directly by clients and will only be used to prove the blocking send update
   via Lob induction. *)
Definition chan_try_blocking_send_atomic_update
  (ch: loc) (cap: w64) (v: V) (γ: chan_names)
  (Φsuccess: iProp Σ) (Φnotready: iProp Σ) : iProp Σ :=
   "#Hperschan" ∷  is_channel ch cap γ ∗
   "Hlogatom" ∷ |={⊤,∅}=>
     ▷∃ s,  "Hoc" ∷  own_channel ch s cap γ ∗
    "Hcont" ∷
    (match s with
     (* Case: Buffered channel. If the buffer is full, the send fails. *)
    | chan_rep.Buffered buff =>
         if decide (length buff < uint.Z cap) then
           (* Success path: add to buffer *)
           (own_channel ch (chan_rep.Buffered (buff ++ [v])) cap γ ={∅,⊤}=∗ Φsuccess)
         else
           (* Buffer full, not selectable *)
           (own_channel ch s cap γ ={∅,⊤}=∗ Φnotready)
     (* Immediate success, a receiver is waiting and we complete the exchange *)
     | chan_rep.RcvWait =>
         own_channel ch (chan_rep.SndDone v) (W64 0) γ ={∅,⊤}=∗ Φsuccess
     (* No exchange in progress, make an offer to receivers. *)
     | chan_rep.Idle =>
          own_channel ch (chan_rep.SndWait v) (W64 0) γ ={∅,⊤}=∗
           |={⊤,∅}=> ▷(
             ∃ s',  "Hoc" ∷ own_channel ch s' (W64 0) γ ∗
             "Hcont" ∷(match s' with
               (* Offer accepted by a receiver, reset the channel and take success continuation *)
              | chan_rep.RcvDone => 
                  own_channel ch chan_rep.Idle (W64 0) γ ={∅,⊤}=∗ Φsuccess
               (* Offer rescinded. *)
              | chan_rep.SndWait v => own_channel ch chan_rep.Idle (W64 0) γ ={∅,⊤}=∗ Φnotready
               (* No other state transitions are legal while an offer is in progress, including close *)
                  | chan_rep.Closed _ => False
                    | _ =>  |={∅, ⊤}=> True
              end))
    (* Exchange in progress *)
     | chan_rep.SndWait _ | chan_rep.RcvDone | chan_rep.SndDone _ => 
         own_channel ch s cap γ ={∅,⊤}=∗ Φnotready
     (* Closed panics on send and this offer logic does not apply to buffered channels. *)
     | _ => False
     end).

Lemma chan_blocking_to_try_update ch cap v γ Φ :
  chan_blocking_send_atomic_update ch cap v γ Φ
  -∗ chan_try_blocking_send_atomic_update ch cap v γ
        Φ
        (chan_blocking_send_atomic_update ch cap v γ Φ).
Proof.
  iIntros "(#Hperschan & Hlogatom)".
  iSplitR "Hlogatom"; first done.
  iMod "Hlogatom" as "Hopen".
  iModIntro.
  iNamed "Hopen". iModIntro. iNamed "Hopen".
  iFrame.

  (* Case analysis on channel state *)
  destruct s; simpl.

  - (* Buffered channel *)
    destruct (decide (length buff < uint.Z cap)) as [Hspace|Hfull].
    + (* Success: space available *)
      iExact "Hcont".
    + (* Failure: buffer full *)
      iIntros "Hoc'". iMod "Hcont" as "_".
      iModIntro. iSplit; [iFrame "#"|].
      iApply fupd_mask_intro; first done. iIntros "Hclose".
      iModIntro. iExists (chan_rep.Buffered buff). iFrame "Hoc'".
      destruct decide; [done|]. iMod "Hclose". iModIntro. done.

  - (* RcvWait: unbuffered channel with receiver waiting *)
    iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. iMod "Hoc".
    iModIntro. iModIntro. iNamed "Hoc". iDestruct "Hoc" as "[Hoc Hrest]". iFrame.
    destruct s'. all: try done.
    { iIntros "Hoc". iMod "Hrest". iModIntro.
      unfold chan_blocking_send_atomic_update. iFrame "#".
      iApply fupd_mask_intro; first done. iIntros "Hc".
      iModIntro. iExists chan_rep.Idle. iFrame.
      iIntros "Hoc". iMod "Hc". iModIntro.
      iApply fupd_mask_intro; first done. iIntros "Hc2".
      iModIntro. iFrame. done. }

  - (* Idle: unbuffered channel *)
    iIntros "Hoc". iMod "Hcont". iModIntro.
    unfold chan_blocking_send_atomic_update. iFrame "#".
    iApply fupd_mask_intro; first done. iIntros "Hc".
    iModIntro. iFrame. done.

  - (* SndWait: channel busy with sender *)
    iIntros "Hoc". iApply "Hcont" in "Hoc". done.

  - (* SndDone: channel in completion state *)
    iIntros "Hoc". iMod "Hcont". iModIntro.
    unfold chan_blocking_send_atomic_update. iFrame "#".
    iApply fupd_mask_intro; first done. iIntros "Hc".
    iModIntro. iFrame. done.

  - (* RcvDone: receiver completion state *)
    iIntros "Hoc". iMod "Hcont". iModIntro.
    unfold chan_blocking_send_atomic_update. iFrame "#".
    iApply fupd_mask_intro; first done. iIntros "Hc".
    iModIntro. iFrame. done.

  - (* Closed: impossible for send *)
    done.
Qed.

(* ================ MAIN LEMMAS ================ *)

Lemma wp_TrySend_nonblocking (ch: loc) (cap: w64) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_nonblocking_send_atomic_update ch cap v γ (Φ (#true)) (Φ (#false))) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TrySend" #t #v #false  {{ Φ }}.
Proof.
  wp_start. iNamed "Hpre". wp_auto_lc 1.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s0.

  { (* Buffered channel *)
    unfold chan_phys. iNamed "phys". wp_auto. wp_if_destruct.

    { (* Space available in buffer *)
      wp_auto. wp_apply wp_slice_literal. iIntros (sl) "Hsl". wp_auto.
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      wp_apply (wp_slice_append with "[$slice $Hsl $slice_cap]").
      iIntros (fr) "(Hfr & Hfrsl & Hsl)". wp_auto_lc 1.

      iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0. destruct decide as [Hok|Hcontra]. all: try word.

      iDestruct (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.Buffered (buff ++ [v]))
                with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch (chan_rep.Buffered (buff ++ [v])) cap γ)%I with "[Hgv1]" as "Hown".
      { iFrame. iPureIntro. unfold chan_rep.buffer_valid.
        rewrite app_length /=. word. }
      iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer Hfr Hfrsl offer Hgv2 $Hlock]").
      { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
      done.
    }

    { (* Buffer full *)
      iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".

      destruct decide.
      - have Hnatlt : sint.Z slice_val.(slice.len_f) < uint.Z cap by word.
        unfold cap_rel in Hcap. destruct Hcap as [Hcapword Hcapnz]. word.
      - iDestruct (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.Buffered buff)
                  with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
        iAssert (own_channel ch (chan_rep.Buffered buff) cap γ)%I with "[$Hgv1]" as "Hown"; first done.
        iMod ("Hcont" with "Hown") as "Hstep". iModIntro. wp_auto.
        wp_apply (wp_Mutex__Unlock with "[$lock state slice slice_cap buffer offer Hgv2 $Hlock]").
        { iModIntro. iFrame. iPureIntro. done. }
        done.
    }
  }

  { (* Idle unbuffered channel *)
    iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.

    iAssert (own_channel ch (chan_rep.Idle) (W64 0) γ)%I with "[Hchanrepfrag]" as "Hown".
    { iSplit. - done. - iPureIntro. simpl. exact I. }
    simpl. iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v offer slice slice_cap buffer auth $Hlock]").
    { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { (* SndWait: sender already waiting *)
    iNamed "phys". wp_auto_lc 1.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".

    iNamed "offer".
    iAssert (own_channel ch (chan_rep.SndWait v0) (W64 0) γ)%I with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro. simpl. exact I. }
    iApply "Hcont" in "Hown". iMod "Hown". iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v offer slice slice_cap buffer auth $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { (* RcvWait: receiver waiting - success case *)
    iNamed "phys". wp_auto_lc 1.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.

    iCombine "auth" "Hchanrepfrag" as "Hfull".
    iMod (ghost_var_update (chan_rep.SndDone v) with "Hfull") as "Hfull'".
    iDestruct "Hfull'" as "[Hauth' Hfrag']".
    iAssert (own_channel ch (chan_rep.SndDone v) (W64 0) γ)%I with "[Hfrag']" as "Hown'".
    { iSplit; [iExact "Hfrag'" | iPureIntro; simpl; exact I]. }
    iMod ("Hcont" with "Hown'") as "HΦtrue". iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v offer slice slice_cap buffer Hauth' $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { (* SndDone: send completion state *)
    iNamed "phys". wp_auto_lc 1. iApply fupd_wp.
    iNamed "HΦ". iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.

    iNamed "offer".
    iAssert (own_channel ch (chan_rep.SndDone v0) (W64 0) γ)%I with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro. simpl. exact I. }
    iApply "Hcont" in "Hown". iMod "Hown". iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v offer slice slice_cap buffer auth $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { (* RcvDone: receive completion state *)
    iNamed "phys". wp_auto_lc 1.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.

    iAssert (own_channel ch (chan_rep.RcvDone) (W64 0) γ)%I with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro. simpl. exact I. }
    iMod ("Hcont" with "Hown") as "HΦtrue". iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v offer slice slice_cap buffer auth $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { (* Closed channel - impossible for send *)
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0. done.
  }
Qed.

Lemma wp_TrySend_blocking (ch: loc) (cap: w64) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_try_blocking_send_atomic_update ch cap v γ (Φ (#true)) (Φ (#false))) -∗
  WP (ch @ (ptrT.id channel.Channel.id) @ "TrySend"#t #v #true) {{ Φ }}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto_lc 1.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".
  destruct s0.
  {
    unfold chan_phys.
    iNamed "phys".
    wp_auto.
    wp_if_destruct.
    {
      wp_auto.
      wp_apply wp_slice_literal.
      iIntros (sl) "Hsl".
      wp_auto.
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      wp_apply (wp_slice_append with "[$slice $Hsl $slice_cap]").
      iIntros (fr) "(Hfr & Hfrsl & Hsl)".
      wp_auto_lc 1.
      iNamed "HΦ".
      iApply fupd_wp.
      iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom".
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.
      destruct decide as [Hok | Hcontra].
      all: try word.
      iDestruct
        (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.Buffered (buff ++ [v]))
          with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch (chan_rep.Buffered (buff ++ [v])) cap γ)%I
        with "[Hgv1]" as "Hown".
      { iFrame. iPureIntro. unfold chan_rep.buffer_valid.
        rewrite app_length /=. word. }
      iMod ("Hcont" with "Hown") as "Hstep".
      iModIntro.
      wp_apply (wp_Mutex__Unlock with "[$lock state buffer Hfr Hfrsl offer Hgv2 $Hlock]").
      { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
      done.
    }
    {
      iNamed "HΦ".
      iApply fupd_wp.
      iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom".
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.
      iDestruct (slice.own_slice_len with "slice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "slice") as "%Hwf".
      destruct decide.
      - have Hnatlt : sint.Z slice_val.(slice.len_f) < uint.Z cap by word.
        unfold cap_rel in Hcap.
        destruct Hcap as [Hcapword Hcapnz].
        word.
      -
      iDestruct
        (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.Buffered buff)
          with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch (chan_rep.Buffered buff) cap γ)%I
        with "[$Hgv1]" as "Hown"; first done.
      iMod ("Hcont" with "Hown") as "Hstep".
      iModIntro.
      wp_auto.
      wp_apply (wp_Mutex__Unlock with "[$lock state slice slice_cap buffer offer Hgv2 $Hlock]").
      { iModIntro. iFrame. iPureIntro. done. }
      done.
    }
  }
  {
    iNamed "phys".
    wp_auto.

    iNamed "HΦ".
    iApply fupd_wp.
    iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.
    simpl.
    iDestruct
      (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.SndWait v)
        with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
    iAssert (own_channel ch (chan_rep.SndWait v) (W64 0) γ)%I
      with "[Hgv1]" as "Hown".
    { iSplit.
      - iExact "Hgv1".
      - iPureIntro; simpl; exact I. }
    iMod ("Hcont" with "Hown") as "Hstep".
    iMod (idle_to_two_snd_wait γ.(offer_name) v with "offer") as "[Hsnd1 Hsnd2]".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer Hgv2 Hsnd2 $Hlock]").
    { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan".
    iNamed "phys".
    unfold chan_phys.
    iDestruct (offer_snd_coherent with "offer Hsnd1") as %Hs.
    destruct Hs.
    {
      subst s0. simpl.
      iNamed "phys".
      wp_auto_lc 1.
      iApply fupd_wp.
      iMod "Hstep".
      iMod (lc_fupd_elim_later with "[$] Hstep") as "Hstep".
      iNamed "Hstep".
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s'.
      iMod (two_snd_wait_to_idle γ.(offer_name) v with "Hsnd1 offer") as "Hidle".
      iDestruct
        (chan_rep_halves_update γ.(state_name) _ _ chan_rep.Idle
          with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch chan_rep.Idle (W64 0) γ)%I
        with "[Hgv1]" as "Hown".
      { iSplit.
        - done.
        - iPureIntro. simpl. exact I. (* buffer_valid (SndWait v) _ = True *) }
      iMod ("Hcont" with "Hown") as "HΦfalse".
      iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer Hgv2 Hidle $Hlock]").
      { iModIntro. unfold chan_inv_inner. iFrame.
        unfold offer_auth. iFrame. iPureIntro. done. }
      done.
    }
    {
      simpl. subst s0.
      iNamed "phys".
      wp_auto_lc 1.
      iApply fupd_wp.
      iMod "Hstep".
      iMod (lc_fupd_elim_later with "[$] Hstep") as "Hstep".
      iNamed "Hstep".
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s'.
      iDestruct
        (chan_rep_halves_update γ.(state_name) _ _ chan_rep.Idle
          with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iNamed "offer".
      iMod (two_snd_wait_to_idle γ.(offer_name) v with "Hsnd1 offer") as "Hidle".
      iAssert (own_channel ch chan_rep.Idle (W64 0) γ)%I
        with "[Hgv1]" as "Hown".
      { iSplit.
        - iExact "Hgv1".
        - iPureIntro. simpl. exact I. }
      (* Feed it to the continuation *)
      iMod ("Hcont" with "Hown") as "HΦtrue".
      iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer Hgv2 Hidle $Hlock]").
      { iModIntro. unfold chan_inv_inner. iFrame.
        unfold offer_auth. iFrame. iPureIntro. done. }
      done.
    }
  }
  {
    iNamed "phys".
    wp_auto_lc 1.
    iApply fupd_wp.
    iNamed "HΦ".
    iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.
    iNamed "offer".
    iAssert (own_channel ch (chan_rep.SndWait v0) (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit.
      - iExact "Hchanrepfrag".
      - iPureIntro. simpl. exact I. (* buffer_valid (SndDone v0) 0 *) }
    iApply "Hcont" in "Hown".
    iMod "Hown".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer auth offer $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame.
      unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }
  {
    iNamed "phys".
    wp_auto_lc 1.
    iNamed "HΦ".
    iApply fupd_wp.
    iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.
    iCombine "auth" "Hchanrepfrag" as "Hfull".
    iMod (ghost_var_update (chan_rep.SndDone v) with "Hfull") as "Hfull'".
    iDestruct "Hfull'" as "[Hauth' Hfrag']".
    iAssert (own_channel ch (chan_rep.SndDone v) (W64 0) γ)%I
      with "[Hfrag']" as "Hown'".
    { iSplit; [ iExact "Hfrag'" | iPureIntro; simpl; exact I ]. }
    iMod ("Hcont" with "Hown'") as "HΦtrue".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer offer Hauth' $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame.
      unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }
  {
    iNamed "phys".
    wp_auto_lc 1.
    iApply fupd_wp.
    iNamed "HΦ".
    iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.
    iNamed "offer".
    iAssert (own_channel ch (chan_rep.SndDone v0) (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit.
      - iExact "Hchanrepfrag".
      - iPureIntro. simpl. exact I. (* buffer_valid (SndDone v0) 0 *) }
    iApply "Hcont" in "Hown".
    iMod "Hown".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer offer auth $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame.
      unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }
  {
    iNamed "phys".
    wp_auto_lc 1.
    iNamed "HΦ".
    iApply fupd_wp.
    iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.
    iAssert (own_channel ch chan_rep.RcvDone (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit.
      - iExact "Hchanrepfrag".
      - iPureIntro. simpl. exact I. (* buffer_valid (SndDone v0) 0 *) }
    iMod ("Hcont" with "Hown") as "HΦtrue".
    iModIntro.
    wp_apply (wp_Mutex__Unlock with "[$lock state v  slice slice_cap buffer offer auth $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame.
      unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }
  {
    iNamed "HΦ".
    iApply fupd_wp.
    iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0. done.
  }
Qed.

Lemma wp_Send (ch: loc) (cap: w64) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_blocking_send_atomic_update ch cap v γ (Φ #())) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v {{ Φ }}.
Proof.
  wp_start. wp_auto_lc 1.
  iDestruct (is_channel_not_null with "[$Hpre]") as "%Hnn".
  iNamed "Hpre". wp_if_destruct.

  - (* Unbuffered case *)
    done.

  - (* Buffered case - retry loop *)
    wp_for. wp_apply wp_TrySend_blocking.
    { iFrame "#". iExists _. done. }

    (* Apply conversion lemma to get try AU *)
    iDestruct (chan_blocking_to_try_update with "HΦ") as "H".
    unfold chan_try_blocking_send_atomic_update.
    iNamed "H". iFrame "#".
    iMod "Hlogatom". iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iModIntro. iNamed "Hlogatom". iFrame. iModIntro.

    (* Case analysis on channel state *)
    destruct s0.

    { (* Buffered channel *)
      destruct decide.
      { (* Success: space available *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
        assert (# false = # false) by set_solver.
        destruct decide; [naive_solver|].
        destruct decide. { wp_auto. done. } { done. }
      }
      { (* Failure: buffer full, continue loop *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
        assert (# true = # true) by set_solver.
        destruct decide. all: try done. wp_auto. wp_for_post. iFrame.
      }
    }

    { (* Idle unbuffered channel *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro.
      iMod "Hoc". iModIntro. iModIntro. iNamed "Hoc". iFrame.

      destruct s'. all: try done.
      { (* Receiver accepted offer - success *)
        iIntros "Hidle". iApply "Hcont" in "Hidle". iMod "Hidle". iModIntro. wp_auto_lc 1.
        assert (# true = # true) by set_solver.
        destruct decide. all: try done. wp_auto. wp_for_post. iFrame.
      }
      { (* Offer rescinded - continue loop *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
        assert (# false = # false) by set_solver.
        destruct decide; [naive_solver|]. destruct decide. all:try done. wp_auto; done.
      }
    }

    { (* RcvWait: receiver waiting - success *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
      assert (# true = # true) by set_solver.
      destruct decide. all:try done. wp_auto_lc 1.
       wp_for_post; iFrame.
    }

    { (* SndWait: channel busy - continue loop *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
      assert (# false = # false) by set_solver.
      destruct decide; [naive_solver|].
      destruct decide; [|naive_solver]. wp_auto. done.
    }

    { (* SndDone: send completion - success *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
      assert (# true = # true) by set_solver.
      destruct decide; [|naive_solver]. wp_auto_lc 1. wp_for_post;iFrame.
    }

    { (* RcvDone: receive completion - success *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
      assert (# true = # true) by set_solver.
      destruct decide; [|naive_solver]. wp_auto_lc 1. wp_for_post;iFrame.
    }

    { (* Closed channel - impossible *)
      done.
    }

    Unshelve. done.
Qed.

End atomic_specs.
