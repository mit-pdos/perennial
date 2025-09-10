From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
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

(* ================ UNBUFFERED CHANNEL HELPERS ================ *)

(* This is used for the offer-based try loop used for blocking select statements. 
   It is not intended to be used directly by clients and only will be used to prove 
   the blocking select and blocking receive that loop around attempts to receive with
   offers and will be proved by induction.
*)
Definition chan_try_blocking_receive_atomic_update
  (ch: loc) (cap: w64) (γ: chan_names)
  (Φsuccess: V → bool → iProp Σ) (Φnotready: iProp Σ) : iProp Σ :=
    "#Hperschan" ∷  is_channel ch cap γ ∗
   "Hlogatom" ∷ |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷  own_channel ch s cap γ ∗
      "Hcont" ∷
    (match s with
    | chan_rep.Buffered (fr :: rest) =>
        own_channel ch (chan_rep.Buffered rest) cap γ ={∅,⊤}=∗ Φsuccess fr true
     |chan_rep.Buffered [] =>   own_channel ch s cap γ ={∅,⊤}=∗ Φnotready

     | chan_rep.SndWait v =>
         own_channel ch chan_rep.RcvDone 0 γ ={∅,⊤}=∗ Φsuccess v true
     | chan_rep.Idle =>
        own_channel ch chan_rep.RcvWait 0 γ ={∅,⊤}=∗
           |={⊤,∅}=> ▷(
             (* Now we have to wait for an external change to the state *)
             ∃ s', own_channel ch s' 0 γ ∗
             (match s' with
              | chan_rep.SndDone v => (* RcvWait was accepted *)
                  own_channel ch chan_rep.Idle 0 γ ={∅,⊤}=∗ Φsuccess v true
              | chan_rep.Closed [] => 
                  own_channel ch (chan_rep.Closed []) 0 γ ={∅,⊤}=∗ Φsuccess (default_val V) false
              | chan_rep.RcvWait =>
                  own_channel ch chan_rep.Idle 0 γ ={∅,⊤}=∗ Φnotready
              | _ => True (* Offer rescinded/no progress *)
              end))
     | chan_rep.Closed draining =>
         (match draining with
          | [] =>
              (own_channel ch s cap γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
          | v :: rest =>
              (own_channel ch (chan_rep.Closed rest) cap γ ={∅,⊤}=∗ Φsuccess v true)
          end)
     | _ => (* busy with other exchange *)
         own_channel ch s 0 γ ={∅,⊤}=∗ Φnotready
     end).

(* ================ GENERIC CHANNEL SPECS ================ *)

(* chan_blocking_receive_atomic_update models the logical behavior of a Go blocking receive.
   It handles buffered, unbuffered, and closed channels in a single, comprehensive specification.
   The core of the logic is a match on the channel's state, delegating to the correct
   sub-specification for each case. *)
Definition chan_blocking_receive_atomic_update ch (cap: w64) (γ: chan_names) (Φsuccess : V → bool → iProp Σ) : iProp Σ :=
   "#Hperschan" ∷ is_channel ch cap γ ∗
   "Hlogatom" ∷ |={⊤,∅}=>
    ▷∃ s,  "Hoc" ∷  own_channel ch s cap γ ∗
    (match s with
    (* Case: Buffered channel with at least one value. *)
    | chan_rep.Buffered (fr :: rest) =>
        own_channel ch (chan_rep.Buffered rest) cap γ ={∅,⊤}=∗ Φsuccess fr true
    (* Case: Buffered channel with no values, N/A for success. *)
    | chan_rep.Buffered [] =>
        |={∅,⊤}=> True
    (* Case: Unbuffered channel with a waiting sender. *)
    | chan_rep.SndWait v =>
          own_channel ch chan_rep.RcvDone 0 γ ={∅,⊤}=∗ Φsuccess v true
    (* Case: Unbuffered channel with no waiting sender. This requires a two-phase handshake. *)
    | chan_rep.Idle =>
          own_channel ch chan_rep.RcvWait 0 γ ={∅,⊤}=∗
               |={⊤,∅}=> ▷∃ s', own_channel ch s' 0 γ ∗
                 (match s' with
                    | chan_rep.SndDone v =>
                        own_channel ch chan_rep.Idle 0 γ ={∅,⊤}=∗ Φsuccess v true
                  | chan_rep.Closed [] =>
                  own_channel ch (chan_rep.Closed []) 0 γ ={∅,⊤}=∗ Φsuccess (default_val V) false
                    (* Other states won't happen on success through this path but client shouldn't have to prove that *)
                    | _ =>
                       |={∅,⊤}=> True
                 end)
    (* Case: Channel is closed. *)
    | chan_rep.Closed draining =>
         (match draining with
          | [] =>
              (own_channel ch s cap γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
          | v :: rest =>
              (own_channel ch (chan_rep.Closed rest) cap γ ={∅,⊤}=∗ Φsuccess v true)
          end)
    (* At the point when we succeed other states aren't involved *)
    | _ => |={∅,⊤}=> True
    end).

(* chan_nonblocking_receive_atomic_update models the logical behavior of a Go non-blocking receive.
   It handles all cases: buffered, unbuffered, and closed. Unlike the blocking version, it fails
   if the condition for success is not met immediately. *)
Definition chan_nonblocking_receive_atomic_update ch (cap: w64) (γ: chan_names) (Φsuccess : V → bool → iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
   "#Hperschan" ∷ is_channel ch cap γ ∗
   "Hlogatom" ∷ |={⊤,∅}=>
    ▷∃ s,  "Hoc" ∷  own_channel ch s cap γ ∗
    match s with
    (* Case: Buffered channel. If the queue is empty, the receive fails. *)
    | chan_rep.Buffered buff =>
         (match buff with
          | [] => (* No items available, not selectable *)
              (own_channel ch s cap γ ={∅,⊤}=∗ Φnotready)
          | v :: rest => (* Success path: dequeue a value *)
              (own_channel ch (chan_rep.Buffered rest) cap γ ={∅,⊤}=∗ Φsuccess v true)
          end)
    (* Case: Unbuffered channel. Succeeds only if there's a waiting sender. *)
    | chan_rep.SndWait v =>
         own_channel ch chan_rep.RcvDone 0 γ ={∅,⊤}=∗
           Φsuccess v true
    (* Case: Channel is closed. *)
    | chan_rep.Closed draining =>
         (match draining with
          | [] => (* Draining is finished(or unbuffered): receive zero value *)
              (own_channel ch s cap γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
          | v :: rest => (* Draining Success Path: receive from buffer *)
              (own_channel ch (chan_rep.Closed rest) cap γ ={∅,⊤}=∗ Φsuccess v true)
          end)
    (* Case: Unbuffered channel without a waiting sender. The receive fails immediately. *)
    | _ =>
        own_channel ch s cap γ ={∅,⊤}=∗ Φnotready
    end.

Lemma chan_blocking_to_try_receive_update ch cap γ Φ :
  chan_blocking_receive_atomic_update ch cap γ Φ
  -∗ chan_try_blocking_receive_atomic_update ch cap γ
        Φ
        (chan_blocking_receive_atomic_update ch cap γ Φ).
Proof.
  iIntros "(#Hperschan & Hlogatom)".
  iSplitR "Hlogatom"; first done.

  (* Open the blocking AU and extract channel state *)
  iMod "Hlogatom" as "Hopen". iModIntro. iModIntro.
  iNamed "Hopen".
  (* Case analysis on channel state *)
  destruct s.

  - (* Buffered channel *)
  iFrame.
    destruct buff as [|v rest].
    +  (* Empty buffer - not ready for try receive *)
      iIntros "Hoc'". iMod "Hopen". iModIntro.
      iSplit; [iFrame "#"|].
      iApply fupd_mask_intro; first done. iIntros "Hclose".
      iModIntro. iFrame. done.
    + (* Has items - success path identical *)
      iFrame.

   - iFrame.
      iIntros "Hoc". iApply "Hopen" in "Hoc".
      iMod "Hoc". iModIntro.
      iMod "Hoc". iModIntro.
      iModIntro. iNamed "Hoc". iDestruct "Hoc" as "[Hoc Hrest]".  iFrame.
    destruct s'. all: try done.
    { iIntros "Hoc". iMod "Hrest". iModIntro.
      unfold chan_blocking_receive_atomic_update. iFrame "#".
      iApply fupd_mask_intro; first done. iIntros "Hc".
      iModIntro. iExists chan_rep.Idle. iFrame.
      iIntros "Hoc". iMod "Hc". iModIntro.
      iApply fupd_mask_intro; first done. iIntros "Hc2".
      iModIntro. iFrame. done. }
    destruct draining; done.
    -
     iFrame. done.
    - iFrame.

       iIntros "Hoc". iMod "Hopen". iModIntro.
      unfold chan_blocking_receive_atomic_update. iFrame "#".
      iApply fupd_mask_intro; first done. iIntros "Hc".
      iModIntro.  iExists (chan_rep.RcvWait).  iFrame.
    - iFrame.
        iIntros "Hoc". iMod "Hopen". iModIntro.
      unfold chan_blocking_receive_atomic_update. iFrame "#".
      iApply fupd_mask_intro; first done. iIntros "Hc".
      iModIntro.  iExists (chan_rep.SndDone v).  iFrame.
    - iFrame.
        iIntros "Hoc". iMod "Hopen". iModIntro.
      unfold chan_blocking_receive_atomic_update. iFrame "#".
      iApply fupd_mask_intro; first done. iIntros "Hc".
      iModIntro.  iExists (chan_rep.RcvDone).  iFrame.
    - iFrame. done.
Qed.

Lemma wp_TryReceive_blocking (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_try_blocking_receive_atomic_update ch cap γ
      (λ v ok, Φ (#true, #v, #ok)%V)
      (Φ (#false, #(default_val V), #true)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TryReceive" #t #true  {{ Φ }}.
Proof.
  wp_start. iNamed "Hpre". wp_auto_lc 1.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s0.

  { (* Buffered channel *)
    unfold chan_phys. iNamed "phys". wp_auto. wp_if_destruct.

    { (* Buffer has items *)
      wp_auto. (* dequeue logic here *)
      iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.

      (* Handle buffer dequeue - similar to send but removing from front *)
      destruct buff as [|v rest].
      - (* Empty buffer contradiction *)
        iAssert (own_channel ch (chan_rep.Buffered []) cap γ)%I
          with "[Hchanrepfrag]" as "Hown".
        { iFrame. iPureIntro. done. }
        iApply "Hcont" in "Hown".
        iMod "Hown". iModIntro. unfold cap_rel in Hcap.
        unfold chan_rep.buffer_valid in Hbuffvalid.
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        rewrite length_nil in Hl.
        replace ( sint.Z slice_val.(slice.len_f) ) with 0 in g by word.
        done.
      - (* Has items - success path *)
        iDestruct (chan_rep_halves_update γ.(state_name) _ _
                    (chan_rep.Buffered rest)
                  with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
        iAssert (own_channel ch (chan_rep.Buffered rest) cap γ)%I
          with "[Hgv1]" as "Hown".
        { iFrame. iPureIntro.
          unfold chan_rep.buffer_valid in *.
          rewrite length_cons in Hbuffvalid. word. }
        iMod ("Hcont" with "Hown") as "Hcont". iModIntro.
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
        { iFrame.  done. }
        iIntros "Hsl". wp_auto.
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
        wp_apply (wp_slice_slice_pure).
        { iPureIntro. word. }
        wp_apply (wp_Mutex__Unlock
                    with "[$lock state slice_cap Hsl buffer offer Hgv2  $Hlock]").
        { iModIntro. unfold chan_inv_inner. iExists (chan_rep.Buffered rest). iFrame.

          have -> : sint.nat (W64 0) = 0%nat by word.
          (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
          simpl.
          iDestruct (own_slice_split_all (W64 1) with "Hsl")
            as "[Hhd Htail]"; first word.
          iFrame.

          iDestruct (own_slice_len with "Hhd") as %[Hlent _].
          iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
          iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
          { word. }
          iApply "H" in "slice_cap". iFrame. done.
        }
        done.
    }

    { (* Empty buffer - not ready *)
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      assert ( sint.Z slice_val.(slice.len_f) = sint.Z (W64 0)).
      { destruct (sint.Z slice_val.(slice.len_f)). all: try done. }

      iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.

      assert (buff = []).
      { destruct buff. { done. } { rewrite H in Hl. naive_solver. } }
      subst buff.

      iAssert (own_channel ch (chan_rep.Buffered []) cap γ)%I
        with "[$Hchanrepfrag]" as "Hown".
      { done. }

      iMod ("Hcont" with "Hown") as "Hstep". iModIntro. wp_auto.
      wp_apply (wp_Mutex__Unlock
                  with "[$lock state buffer slice slice_cap offer auth $Hlock]").
      { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
      iFrame.
    }
  }

  { (* Idle unbuffered channel - handshake required *)
    iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.

    (* Start receive handshake - similar to send but receiver side *)
    iDestruct (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.RcvWait)
              with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
    iAssert (own_channel ch chan_rep.RcvWait (W64 0) γ)%I
      with "[Hgv1]" as "Hown".
    { iSplit. - iExact "Hgv1". - iPureIntro; simpl; exact I. }
    iMod ("Hcont" with "Hown") as "Hstep".

    (* Set up receive tokens - mirror of send handshake *)
    iMod (idle_to_two_rcv_wait γ.(offer_name) with "offer") as "[Hrcv1 Hrcv2]".
    iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer Hgv2 Hrcv2 $Hlock]").
    { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }

    (* Re-acquire lock to check result *)
    wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
    iNamed "Hchan". iNamed "phys". unfold chan_phys.
    iDestruct (offer_rcv_coherent with "offer Hrcv1") as %Hs.
    destruct Hs.
    + (* Handshake failed - not ready *)
      subst s0. simpl. iNamed "phys". wp_auto_lc 1. iApply fupd_wp.
      iMod "Hstep". iMod (lc_fupd_elim_later with "[$] Hstep") as "Hstep".
      iNamed "Hstep". iDestruct "Hstep" as "[Hoc Hrest]". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s'.

      iMod (two_rcv_wait_to_idle γ.(offer_name) with "Hrcv1 offer") as "Hidle".
      iDestruct (chan_rep_halves_update γ.(state_name) _ _ chan_rep.Idle
                with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch chan_rep.Idle (W64 0) γ)%I
        with "[Hgv1]" as "Hown".
      { iSplit. - done. - iPureIntro. simpl. exact I. }
      simpl.
      iMod ("Hrest" with "Hown") as "HΦfalse". iModIntro.
      wp_apply (wp_Mutex__Unlock
                  with "[$lock state v slice slice_cap buffer Hgv2 Hidle $Hlock]").
      { iModIntro. unfold chan_inv_inner. iFrame.
        unfold offer_auth. iFrame. iPureIntro. done. }
      done.

    + destruct H as [v0 Hv]. subst s0. iNamed "phys". wp_auto_lc 1. iApply fupd_wp.
      iMod "Hstep". iMod (lc_fupd_elim_later with "[$] Hstep") as "Hstep".
      iNamed "Hstep". iDestruct "Hstep" as "[Hoc Hrest]". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s'.

      iDestruct (chan_rep_halves_update γ.(state_name) _ _ chan_rep.Idle
                with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iNamed "offer".
      iMod (two_rcv_wait_to_idle γ.(offer_name) with "Hrcv1 offer") as "Hidle".
      iAssert (own_channel ch chan_rep.Idle (W64 0) γ)%I
        with "[Hgv1]" as "Hown".
      { iSplit. - iExact "Hgv1". - iPureIntro. simpl. exact I. }
      iMod ("Hrest" with "Hown") as "HΦtrue". iModIntro.
      wp_apply (wp_Mutex__Unlock
                  with "[$lock state v slice slice_cap buffer Hgv2 Hidle $Hlock]").
      { iModIntro. unfold chan_inv_inner. iFrame.
        unfold offer_auth. iFrame. iPureIntro. done. }
      done.
  }

  (* Continue with other cases following the same pattern... *)
  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.

    (* Start receive handshake - similar to send but receiver side *)
    iDestruct (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.RcvDone)
              with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
    iAssert (own_channel ch chan_rep.RcvDone (W64 0) γ)%I
      with "[Hgv1]" as "Hown".
    { iSplit. - iExact "Hgv1". - iPureIntro; simpl; exact I. }
    iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state slice slice_cap buffer v Hgv2 offer  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iAssert (own_channel ch chan_rep.RcvWait (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro; simpl; exact I. }
    iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer  offer  auth  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iAssert (own_channel ch (chan_rep.SndDone v) (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro; simpl; exact I. }
    iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer offer  auth  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iAssert (own_channel ch (chan_rep.RcvDone) (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro; simpl; exact I. }
    iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer offer  auth  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys".
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    destruct draining.
    {
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.
      unfold chan_phys. iNamed "phys".
      iAssert (own_channel ch (chan_rep.Closed []) cap γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iSplit. - iExact "Hchanrepfrag". - iPureIntro. done. }
      iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
      wp_auto. wp_if_destruct.
      { unfold chan_rep.buffer_valid in Hbuffvalid. Search "own_empty_slice".
        iDestruct (own_slice_len with "slice") as "%".
        destruct H as [Hlen Hnonneg]. rewrite length_nil in Hlen. word.
      }
      wp_auto.
      wp_apply (wp_Mutex__Unlock
                  with "[$lock   offer slice slice_cap buffer  auth state  $Hlock]").
      { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. }
      done.
    }
    {
      unfold chan_phys. iNamed "phys".
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.
      iDestruct (chan_rep_halves_update γ.(state_name) _ _
                  (chan_rep.Closed draining)
                with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch (chan_rep.Closed (draining)) cap γ)%I
        with "[Hgv1]" as "Hown".
      { iSplit. - iExact "Hgv1". - iPureIntro.
        unfold chan_rep.buffer_valid in *.
        rewrite length_cons in Hbuffvalid. word. }

      iMod ("Hcont" with "Hown") as "Hstep". iModIntro.
      wp_auto.
      have Hpos : 0 ≤ sint.Z (W64 0) by word.
      have Hlookup0 : (v :: draining) !! 0%nat = Some v by done.
      iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
      { exact Hpos. }
      { done. }
      iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
      iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
      rewrite length_cons in Hlen_eq.
      assert (sint.Z slice_val.(slice.len_f) > sint.Z (W64 0)) by word.
      wp_if_destruct.
      {
        wp_auto.
        iDestruct (own_slice_elem_acc with "Hclose") as "[Hcell Hclose]".
        { exact Hpos. }
        { done. }
        iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
        have Hlt : 0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len_f).
        { move: Hlen_eq; simpl.  (* length (v::draining) = S (length draining) *)
          (* sint.nat len = S _  ⇒  sint.Z len > 0 *)
          word. }
        wp_auto.
        have H0 : (v :: draining) !! 0%nat = Some v by done.
        wp_apply ((wp_load_slice_elem slice_val 0
                    ( <[sint.nat (W64 0):=v]>
                      (<[sint.nat (W64 0):=v]> (v :: draining))
                    ))
                   with "[Hclose]"). all: try word.
        { iFrame. done. }
        iIntros "Hsl". wp_auto.
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
        wp_apply (wp_slice_slice_pure).
        { iPureIntro. word. }
        wp_apply (wp_Mutex__Unlock
                    with "[$lock state slice_cap Hsl buffer offer Hgv2  $Hlock]").
        { iModIntro. unfold chan_inv_inner. iExists (chan_rep.Closed draining). iFrame.
          unfold chan_phys.
          destruct draining.
          {
            have -> : sint.nat (W64 0) = 0%nat by word.
            (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
            iDestruct ((own_slice_split_all 1 slice_val (DfracOwn 1)
                        ([v])) with "Hsl") as "(Hhd & Htail)"; first word.
            replace ( sint.nat (W64 1)) with (1%nat) by done. simpl. iFrame.
            iDestruct (own_slice_len with "Hhd") as %[Hlent _].
            iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
            iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
            { word. }
            iApply "H" in "slice_cap". done.
          }
          {
            have -> : sint.nat (W64 0) = 0%nat by word.
            (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
            simpl.
            iDestruct (own_slice_split_all (W64 1) with "Hsl") as "[Hhd Htail]"; first word.
            replace ( sint.nat (W64 1)) with (1%nat) by done. simpl. iFrame.
            iDestruct (own_slice_len with "Hhd") as %[Hlent _].
            iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
            iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
            { word. }
            iApply "H" in "slice_cap". iFrame. done.
          }
        }
        done.
      }
      done.
    }
  }
Qed.

(* wp_Receive is the main lemma that links the logical specification to the concrete Go code.
   It states that for any postcondition Φ, if you have the proper preconditions,
   the Go "Receive" method will terminate and satisfy the atomic update specified. *)
Lemma wp_Receive (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_blocking_receive_atomic_update ch cap γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #() {{ Φ }}.
Proof.
  wp_start. wp_auto_lc 1.
  iDestruct (is_channel_not_null with "[$Hpre]") as "%Hnn".
  iNamed "Hpre". wp_if_destruct.

  - (* Unbuffered case *)
    done.

  - (* Buffered case - retry loop *)
    wp_for.  wp_apply wp_TryReceive_blocking.
    { iFrame "#". iExists _. done. }

    (* Apply conversion lemma to get try AU *)
    iDestruct (chan_blocking_to_try_receive_update with "HΦ") as "H".
    unfold chan_try_blocking_receive_atomic_update.
    iNamed "H". iFrame "#".
    iMod "Hlogatom". iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iModIntro. iNamed "Hlogatom". iFrame. iModIntro.

    (* Case analysis on channel state *)
    destruct s0.

    { (* Buffered channel *)
      destruct buff as [|v rest].
      { (* Empty buffer - continue loop *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
        assert (# false = # false) by set_solver.
        wp_for_post. iFrame "Hoc". iFrame.
      }
      { (* Has items - success *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
        assert (# true = # true) by set_solver.
        wp_for_post.  iFrame.
      }
    }

    { (* Idle unbuffered channel *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro.
      iMod "Hoc". iModIntro. iModIntro. iNamed "Hoc".

      destruct s'. all: try (iFrame;done).
       { (* buffer *)
         iExists (chan_rep.Buffered buff).
        iFrame.

      }
      { (* Sender accepted offer - success *)
        iFrame. iExists (chan_rep.Idle). iFrame.
      }
      { (* Sender accepted offer - success *)
        iFrame. iDestruct "Hoc" as "[Hoc Hup]". iExists (chan_rep.SndWait v). iFrame.
      }
      { (* Sender accepted offer - success *)
        iFrame.
        iFrame. iDestruct "Hoc" as "[Hoc Hup]". iExists (chan_rep.RcvWait). iFrame.
        iIntros "Hidle". iApply "Hup" in "Hidle". iMod "Hidle". iModIntro. wp_auto_lc 1.
        wp_for_post. iFrame "Hidle". iFrame.
      }
       { (* Sender accepted offer - success *)
        iFrame.
         iDestruct "Hoc" as "[Hoc Hup]". iExists (chan_rep.SndDone v). iFrame.
        iIntros "Hsw". iApply "Hup" in "Hsw". iMod "Hsw". iModIntro. wp_auto_lc 1.
        wp_for_post. done.
      }
      {
        iFrame. iDestruct "Hoc" as "[Hoc Hup]". iExists (chan_rep.RcvDone). iFrame.
      }
      {
        iFrame. iDestruct "Hoc" as "[Hoc Hup]". destruct draining.
        {
          iExists (chan_rep.Closed []). iFrame.
          iIntros "Hoc".
          iApply "Hup" in "Hoc". iMod "Hoc". iModIntro. wp_auto. wp_for_post. iFrame.
        }
         {
          iExists (chan_rep.Closed (v :: draining)). iFrame.
          }
        }
      }


    { (* Other busy states - continue loop *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
      assert (# false = # false) by set_solver.
      iFrame. wp_for_post. iFrame.
    }
     { (* Other busy states - continue loop *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
      assert (# false = # false) by set_solver.
      iFrame. wp_for_post. iFrame.
      }
       { (* Other busy states - continue loop *)
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
      assert (# false = # false) by set_solver.
      iFrame. wp_for_post. iFrame.
    }
    {
      iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto_lc 1.
      assert (# false = # false) by set_solver.
      iFrame. wp_for_post. iFrame.
    }


    { (* Closed channel with draining *)
      destruct draining as [|v rest].
      { (* Empty - success with default value *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
        assert (# true = # true) by set_solver.
        iFrame.
        wp_for_post.
        done.
      }
      { (* Has items - success *)
        iIntros "Hoc". iApply "Hcont" in "Hoc". iMod "Hoc". iModIntro. wp_auto.
        assert (# true = # true) by set_solver.
        iFrame. wp_for_post;done.
      }
    }

    Unshelve. done.
Qed.

(* This lemma proves that the `TryReceive(false)` Go function call satisfies
   the `chan_nonblocking_receive_atomic_update` specification.
   The postcondition `Φ` must handle all three possible return values from `TryReceive`:
   `(selected, value, ok)`. *)
Lemma wp_TryReceive_nonblocking (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_nonblocking_receive_atomic_update ch cap γ
      (λ v ok, Φ (#true, #v, #ok)%V)
      (Φ (#false, #(default_val V), #true)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TryReceive" #t #false {{ Φ }}.
Proof.
  wp_start. iNamed "Hpre". wp_auto_lc 1.
  wp_apply (wp_Mutex__Lock with "[$lock]") as "[Hlock Hchan]".
  iNamed "Hchan".

  (* Case analysis on channel state *)
  destruct s0.

  { (* Buffered channel *)
    unfold chan_phys. iNamed "phys". wp_auto. wp_if_destruct.

    { (* Buffer has items *)
      wp_auto. 
      iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.

      (* Handle buffer dequeue - similar to send but removing from front *)
      destruct buff as [|v rest].
      - (* Empty buffer contradiction *)
        iAssert (own_channel ch (chan_rep.Buffered []) cap γ)%I
          with "[Hchanrepfrag]" as "Hown".
        { iFrame. iPureIntro. done. }
        iApply "Hlogatom" in "Hown".
        iMod "Hown". iModIntro. unfold cap_rel in Hcap.
        unfold chan_rep.buffer_valid in Hbuffvalid.
        iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
        rewrite length_nil in Hl.
        replace ( sint.Z slice_val.(slice.len_f) ) with 0 in g by word.
        done.
      - (* Has items - success path *)
        iDestruct (chan_rep_halves_update γ.(state_name) _ _
                    (chan_rep.Buffered rest)
                  with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
        iAssert (own_channel ch (chan_rep.Buffered rest) cap γ)%I
          with "[Hgv1]" as "Hown".
        { iFrame. iPureIntro.
          unfold chan_rep.buffer_valid in *.
          rewrite length_cons in Hbuffvalid. word. }
        iMod ("Hlogatom" with "Hown") as "Hcont". iModIntro.
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
        wp_apply (wp_Mutex__Unlock
                    with "[$lock state slice_cap Hsl buffer offer Hgv2  $Hlock]").
        { iModIntro. unfold chan_inv_inner. iExists (chan_rep.Buffered rest). iFrame.

          have -> : sint.nat (W64 0) = 0%nat by word.
          (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
          simpl.
          iDestruct (own_slice_split_all (W64 1) with "Hsl")
            as "[Hhd Htail]"; first word.
          iFrame.

          iDestruct (own_slice_len with "Hhd") as %[Hlent _].
          iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
          iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
          { word. }
          iApply "H" in "slice_cap". iFrame. done.
        }
        done.
    }

    { (* Empty buffer - not ready *)
      iDestruct (own_slice_len with "slice") as "[%Hl %Hcap2]".
      assert ( sint.Z slice_val.(slice.len_f) = sint.Z (W64 0)).
      {
        destruct (sint.Z slice_val.(slice.len_f)). all: try done.
      }

      iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
      iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
      iNamed "Hlogatom". iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.

      assert (buff = []).
      { destruct buff. { done. } { rewrite H in Hl. naive_solver. } }
      subst buff.

      iAssert (own_channel ch (chan_rep.Buffered []) cap γ)%I
        with "[$Hchanrepfrag]" as "Hown".
      { done. }

      iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro. wp_auto.
      wp_apply (wp_Mutex__Unlock
                  with "[$lock state buffer slice slice_cap offer auth $Hlock]").
      { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
      iFrame.
    }
  }

  { (* Idle unbuffered channel  *)
    iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
    subst s0.

    iDestruct (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.Idle)
              with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
    iAssert (own_channel ch chan_rep.Idle (W64 0) γ)%I
      with "[Hgv1]" as "Hown".
    { iSplit. - iExact "Hgv1". - iPureIntro; simpl; exact I. }
    iMod ("Hlogatom" with "Hown") as "Hstep".
    iModIntro.

    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer offer Hgv2 $Hlock]").
    { iModIntro. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  (* Continue with other cases following the same pattern... *)
  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.

    (* Start receive handshake - similar to send but receiver side *)
    iDestruct (chan_rep_halves_update γ.(state_name) _ _ (chan_rep.RcvDone)
              with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
    iAssert (own_channel ch chan_rep.RcvDone (W64 0) γ)%I
      with "[Hgv1]" as "Hown".
    { iSplit. - iExact "Hgv1". - iPureIntro; simpl; exact I. }
    iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state slice slice_cap buffer v Hgv2 offer  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iAssert (own_channel ch chan_rep.RcvWait (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro; simpl; exact I. }
    iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer  offer  auth  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iAssert (own_channel ch (chan_rep.SndDone v) (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro; simpl; exact I. }
    iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer offer  auth  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys". wp_auto.
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom". iNamed "Hoc".
    iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq". subst s0.
    iAssert (own_channel ch (chan_rep.RcvDone) (W64 0) γ)%I
      with "[Hchanrepfrag]" as "Hown".
    { iSplit. - iExact "Hchanrepfrag". - iPureIntro; simpl; exact I. }
    iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro.
    wp_apply (wp_Mutex__Unlock
                with "[$lock state v slice slice_cap buffer offer  auth  $Hlock]").
    { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. iPureIntro. done. }
    done.
  }

  { iNamed "phys".
    iNamed "HΦ". iApply fupd_wp. iMod "Hlogatom".
    iMod (lc_fupd_elim_later with "[$] Hlogatom") as "Hlogatom".
    iNamed "Hlogatom".
    destruct draining.
    {
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.
      unfold chan_phys. iNamed "phys".
      iAssert (own_channel ch (chan_rep.Closed []) cap γ)%I
        with "[Hchanrepfrag]" as "Hown".
      { iSplit. - iExact "Hchanrepfrag". - iPureIntro. done. }
      iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro.
      wp_auto. wp_if_destruct.
      { unfold chan_rep.buffer_valid in Hbuffvalid. Search "own_empty_slice".
        iDestruct (own_slice_len with "slice") as "%".
        destruct H as [Hlen Hnonneg]. rewrite length_nil in Hlen. word.
      }
      wp_auto.
      wp_apply (wp_Mutex__Unlock
                  with "[$lock   offer slice slice_cap buffer  auth state  $Hlock]").
      { iModIntro. unfold chan_inv_inner. iFrame. unfold offer_auth. iFrame. }
      done.
    }
    {
      unfold chan_phys. iNamed "phys".
      iNamed "Hoc".
      iDestruct (chan_rep_agree with "[$auth] [$Hchanrepfrag]") as "%Hseq".
      subst s0.
      iDestruct (chan_rep_halves_update γ.(state_name) _ _
                  (chan_rep.Closed draining)
                with "[$auth] [$Hchanrepfrag]") as ">[Hgv1 Hgv2]".
      iAssert (own_channel ch (chan_rep.Closed (draining)) cap γ)%I
        with "[Hgv1]" as "Hown".
      { iSplit. - iExact "Hgv1". - iPureIntro.
        unfold chan_rep.buffer_valid in *.
        rewrite length_cons in Hbuffvalid. word. }

      iMod ("Hlogatom" with "Hown") as "Hstep". iModIntro.
      wp_auto.
      have Hpos : 0 ≤ sint.Z (W64 0) by word.
      have Hlookup0 : (v :: draining) !! 0%nat = Some v by done.
      iDestruct (own_slice_elem_acc with "slice") as "[Hcell Hclose]".
      { exact Hpos. }
      { done. }
      iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
      iDestruct (own_slice_len with "Hclose") as %(Hlen_eq & Hnonneg).
      rewrite length_cons in Hlen_eq.
      assert (sint.Z slice_val.(slice.len_f) > sint.Z (W64 0)) by word.
      wp_if_destruct.
      {
        wp_auto.
        iDestruct (own_slice_elem_acc with "Hclose") as "[Hcell Hclose]".
        { exact Hpos. }
        { done. }
        iSpecialize ("Hclose" $! v with "Hcell").  (* gives back [slice_val ↦* (v::draining)] *)
        have Hlt : 0 ≤ sint.Z (W64 0) < sint.Z slice_val.(slice.len_f).
        { move: Hlen_eq; simpl.  (* length (v::draining) = S (length draining) *)
          (* sint.nat len = S _  ⇒  sint.Z len > 0 *)
          word. }
        wp_auto.
        have H0 : (v :: draining) !! 0%nat = Some v by done.
        wp_apply ((wp_load_slice_elem slice_val 0
                    ( <[sint.nat (W64 0):=v]>
                      (<[sint.nat (W64 0):=v]> (v :: draining))
                    ))
                   with "[Hclose]"). all: try word.
        { iFrame. done. }
        iIntros "Hsl". wp_auto.
        iDestruct (own_slice_cap_wf with "slice_cap") as %Hwf.
        wp_apply (wp_slice_slice_pure).
        { iPureIntro. word. }
        wp_apply (wp_Mutex__Unlock
                    with "[$lock state slice_cap Hsl buffer offer Hgv2  $Hlock]").
        { iModIntro. unfold chan_inv_inner. iExists (chan_rep.Closed draining). iFrame.
          unfold chan_phys.
          destruct draining.
          {
            have -> : sint.nat (W64 0) = 0%nat by word.
            (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
            iDestruct ((own_slice_split_all 1 slice_val (DfracOwn 1)
                        ([v])) with "Hsl") as "(Hhd & Htail)"; first word.
            replace ( sint.nat (W64 1)) with (1%nat) by done. simpl. iFrame.
            iDestruct (own_slice_len with "Hhd") as %[Hlent _].
            iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
            iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
            { word. }
            iApply "H" in "slice_cap". done.
          }
          {
            have -> : sint.nat (W64 0) = 0%nat by word.
            (* <[0:=v]>(<[0:=v]> [v]) = [v] *)
            simpl.
            iDestruct (own_slice_split_all (W64 1) with "Hsl") as "[Hhd Htail]"; first word.
            replace ( sint.nat (W64 1)) with (1%nat) by done. simpl. iFrame.
            iDestruct (own_slice_len with "Hhd") as %[Hlent _].
            iDestruct (own_slice_cap_wf with "slice_cap") as %Hlen_le_cap.
            iDestruct (own_slice_cap_slice_f (slice_val) (W64 1) (DfracOwn 1)) as "H".
            { word. }
            iApply "H" in "slice_cap". iFrame. done.
          }
        }
        done.
      }
      done.
    }
  }
Qed.

End atomic_specs.
