Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.

(** * Single Producer Single Consumer (SPSC) Channel Verification

    This file provides a high-level abstraction for single-producer single-consumer
    channels built on top of the low-level channel verification. The SPSC abstraction
    provides stronger guarantees by tracking the history of sent and received values.

    Key features:
    - Producer maintains exclusive send permission with history tracking
    - Consumer maintains exclusive receive permission with history tracking
    - Ghost state tracks sent/received histories with fractional permissions
    - Invariant maintains relationship: sent = received ++ in_flight
    - Support for resource protocols P (per-value) and R (final state)
*)

#[local] Transparent is_chan own_chan.

Section spsc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].

(** ** Ghost State Names *)

Record spsc_names := {
  chan_name : chan_names;      (* Underlying channel ghost state *)
  spsc_sent_name : gname;      (* History of sent values *)
  spsc_recv_name : gname       (* History of received values *)
}.


(* Producer and Consumer Predicates *)

(** Producer maintains (1/2) permission of sent history *)
Definition spsc_producer (γ:spsc_names) (sent:list V) : iProp Σ :=
    dghost_var γ.(spsc_sent_name) (DfracOwn (1/2)) sent.

(** Consumer maintains (1/2) permission of received history *)
Definition spsc_consumer (γ:spsc_names) (received:list V) : iProp Σ :=
    dghost_var γ.(spsc_recv_name) (DfracOwn (1/2)) received.

(** ** In-Flight Values *)

(** Values that have been sent but not yet received *)
Definition inflight (s : chanstate.t V) : list V :=
  match s with
  | chanstate.Buffered buff => buff
  | chanstate.SndPending v | chanstate.SndCommit v => [v]
  | chanstate.Closed drain => drain
  | _ => []
  end.

(** ** SPSC Channel Invariant *)

(** The main SPSC channel predicate.

    Parameters:
    - P: Resource associated with each value (maintained while in-flight)
    - R: Final resource when channel is closed and drained

    The invariant maintains:
    - sent = received + inflight(channel_state)
    - P holds for all in-flight values
    - When closed, producer permission is parked to prevent further sends
    - When closed and drained, consumer gets R
*)
Definition is_spsc (γ:spsc_names) (ch:loc)
                   (P: Z -> V → iProp Σ) (R: list V → iProp Σ) : iProp Σ :=
    is_chan ch γ.(chan_name) V ∗
    inv nroot (
      ∃ s sent recv,
        "Hch"    ∷ own_chan γ.(chan_name) V s ∗
        "HsentI" ∷ dghost_var γ.(spsc_sent_name) (DfracOwn (1/2)) sent ∗
        "HrecvI" ∷ dghost_var γ.(spsc_recv_name) (DfracOwn (1/2)) recv ∗
        "%Hrel"  ∷ ⌜sent = recv ++ inflight s⌝ ∗
        (match s with
        (* P holds for all buffered values *)
        | chanstate.Buffered buff =>
            [∗ list] i ↦ v ∈ buff, P ((length recv) + i) v
        (* P holds for pending/committed values *)
        | chanstate.SndPending v | chanstate.SndCommit v =>
            P (length recv) v
        (* Closed channel: park producer permission, provide R when drained *)
        | chanstate.Closed [] =>
            spsc_producer γ sent ∗ (R sent ∨ spsc_consumer γ sent)
        | chanstate.Closed drain =>
            ([∗ list] i ↦ v ∈ drain, P ((length recv) + i) v) ∗
            spsc_producer γ sent ∗
            (R sent ∨ spsc_consumer γ sent)
        | _ => True
        end)
    )%I.

(** ** Initialization *)

(** Create an SPSC channel from a basic channel *)
Lemma start_spsc ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ) γ:
  is_chan ch γ V -∗
  (own_chan γ V chanstate.Idle) ∨ (own_chan γ V (chanstate.Buffered [])) ={⊤}=∗
  (∃ γspsc, is_spsc γspsc ch P R ∗  spsc_producer γspsc []  ∗  spsc_consumer γspsc []) .
Proof.
  iIntros "#Hch Hoc".

  (* Allocate ghost variables for sent and received histories *)
  iMod (dghost_var_alloc ([] : list V)) as (γsent) "[HsentA HsentF]".
  iMod (dghost_var_alloc ([] : list V)) as (γrecv) "[HrecvA HrecvF]".

  (* Create the spsc_names record *)
  set (γspsc := {| chan_name := γ; spsc_sent_name := γsent; spsc_recv_name := γrecv |}).
  iExists (γspsc).

  (* Allocate the invariant *)
  iMod (inv_alloc nroot _ with "[Hoc HsentA HrecvA]") as "$".
  {
    iDestruct "Hoc" as "[Hoc|Hoc]".
    (* Prove the invariant holds initially *)
  {
    simpl.
    iNext. iExists chanstate.Idle, [], []. iFrame.
    iPureIntro. simpl. done.
    }
    {
       iNext. iExists (chanstate.Buffered []), [], []. iFrame.
       simpl.
       iFrame.
    iPureIntro. simpl. done.
    }
  }

  (* Construct the final result *)
  iModIntro.
  iFrame "#∗".
Qed.

(** ** Receive Operation *)

Lemma spsc_rcv_au γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                      (received : list V) Φ :
  is_spsc γ ch P R -∗
  £1 ∗ £1 -∗
  spsc_consumer γ received -∗
  (▷ ∀ v (ok:bool),
     (if ok then P (length received) v ∗ spsc_consumer γ (received ++ [v])
            else R received ∗ ⌜ v = (zero_val V) ⌝) -∗
     Φ v ok) -∗
  recv_au γ.(chan_name) V Φ.
Proof.
  iIntros "#Hspsc [Hlc1 Hlc2] Hcons Hcont".
  unfold is_spsc.
  iDestruct "Hspsc" as "[Hchan Hinv]".

  (* Open the SPSC invariant to provide the atomic update *)
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".

  (* Establish agreement between our received and invariant's recv *)
  iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.

  (* Provide recv_au *)
  unfold recv_au.
  iExists s. iFrame "Hch".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.

  (* Case analysis on channel state *)
  destruct s; try done.

  { (* Case: Buffered channel *)
    destruct buff as [|v rest].
    { (* Empty buffer - no change to invariant *) done. }
    { (* Non-empty buffer - can receive immediately *)
      iIntros "Hoc".

      (* Update received history *)
      iCombine "Hcons HrecvI" as "Hrecv_full".
      iMod (dghost_var_update (recv ++ [v]) with "Hrecv_full") as "[HrecvI_new Hcons_new]".

      (* Extract P v from the big star list *)
      iDestruct (big_sepL_cons with "Hinv_open") as "[HPv Hrest]".

      (* Close invariant with updated state *)
      iMod "Hmask".
      iMod ("Hinv_close" with "[Hoc HsentI HrecvI_new Hrest]") as "_".
      {
        iNext. iExists (chanstate.Buffered rest), sent, (recv ++ [v]).
        iFrame. rewrite  length_app.

        rewrite singleton_length. iSplitR "Hrest". {
        iPureIntro. rewrite Hrel. simpl. rewrite <- app_assoc. reflexivity.
        }
        {
          iApply (big_sepL_proper _ _ rest with "Hrest").
intros k y z.
replace (length recv + S k) with ((length recv + 1)%nat + k) by lia.
done.

      }
      }

      (* Apply continuation with ok=true *)
      iModIntro. iApply "Hcont". iFrame.
      replace  (length recv + 0%nat)  with (Z.of_nat (length recv)) by lia.
      done.
    }
  }

  { (* Case: Idle channel - register as receiver *)
    iIntros "Hoc".

    (* Close invariant with RcvPending state *)
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI]") as "_".
    {
      iNext. iExists chanstate.RcvPending, sent, recv.
      iFrame.
      iPureIntro. rewrite Hrel. simpl. done.
    }

    (* Provide recv_nested_au for completion *)
    iModIntro. unfold recv_nested_au.
    iInv "Hinv" as "Hinv_open2" "Hinv_close".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
    iNamed "Hinv_open2".

    (* Establish agreement between our received and invariant's recv *)
    iDestruct (dghost_var_agree with "Hcons HrecvI") as %->.

    unfold recv_au.
    iExists s. iFrame "Hch".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask1"].
    iNext.

    (* Should be SndCommit v when sender completes *)
    destruct s; try done.
    {
      (* SndCommit case - complete the handshake *)
      iCombine "Hcons HrecvI" as "Hrcv_full".
      iMod (dghost_var_update (recv0 ++ [v]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
      iIntros "Hoc".
      iMod "Hmask1".
      iMod ("Hinv_close" with "[HsentI HrecvI_new Hoc]") as "_".
      {
        iNext. iExists chanstate.Idle, sent0, (recv0 ++ [v]).
        iFrame.
        iPureIntro. rewrite Hrel0. simpl. rewrite app_nil_r. done.
      }
      iModIntro. iApply "Hcont". iFrame.
    }
    { (* Closed empty case *)
      destruct drain as [|v rest].
      {
        iIntros "Hoc".
        iMod "Hmask1".
        iDestruct "Hinv_open2" as "(H1 & H2)".
        iDestruct "H2" as "[H2 | H3]".
        {
          iMod ("Hinv_close" with "[HsentI HrecvI Hoc H1 Hcons]") as "H".
          {
            iNext. iFrame.
            iSplitR "HrecvI".
            { iPureIntro. done. }
            iRight. unfold spsc_consumer. subst sent0. unfold inflight. rewrite app_nil_r. done.
          }
          iModIntro. iApply "Hcont". iFrame.
          subst sent0. unfold inflight. rewrite app_nil_r. iFrame.
          done.
        }
        {
          iExFalso.
          unfold spsc_consumer.
          iCombine "Hcons HrecvI" as "Hfull".
          iDestruct (dghost_var_valid_2 with "Hfull H3") as "[%Hvalid _]".
          done.
        }
      }
      { done. }
    }
  }

  { (* Case: SndPending - fast path completion *)
    iIntros "Hcont1".
    iMod "Hmask".
    iCombine "Hcons HrecvI" as "Hrcv_full".
    iMod (dghost_var_update (recv ++ [v]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
    iMod ("Hinv_close" with "[HsentI HrecvI_new Hcont1]") as "H".
    {
      iNext. iFrame. iPureIntro.
      unfold inflight in *. rewrite app_nil_r. done.
    }
    iModIntro. iApply "Hcont". iFrame.
  }

  { (* Case: Closed channel *)
    destruct drain as [|v rest].
    { (* Empty closed channel - return R *)
      iIntros "Hoc".
      iMod "Hmask".
      iDestruct "Hinv_open" as "(H1 & H2)".
      iDestruct "H2" as "[H2 | H3]".
      {
        iMod ("Hinv_close" with "[HsentI HrecvI Hoc H1 Hcons]") as "H".
        {
          iNext. iFrame.
          iSplitR "HrecvI".
          { iPureIntro. done. }
          iRight. unfold spsc_consumer. subst sent. unfold inflight. rewrite app_nil_r. done.
        }
        iModIntro. iApply "Hcont". iFrame.
        subst sent. unfold inflight. rewrite app_nil_r. iFrame.
        done.
      }
      {
        iExFalso.
        unfold spsc_consumer.
        iCombine "Hcons HrecvI" as "Hfull".
        iDestruct (dghost_var_valid_2 with "Hfull H3") as "[%Hvalid _]".
        done.
      }
    }
    { (* Closed channel with drain values *)
      iIntros "Hoc".
      iCombine "Hcons HrecvI" as "Hrcv_full".
      iMod (dghost_var_update (recv ++ [v]) with "Hrcv_full") as "[HrecvI_new Hcons_new]".
      iMod "Hmask".
      iDestruct "Hinv_open" as "(H1 & H2 & H3)".
      iDestruct "H3" as "[H4 | H5]".
      {
        destruct rest.
        {
          iMod ("Hinv_close" with "[HsentI Hoc H2 H4 Hcons_new]") as "H".
          {
            iNext. iFrame. iSplitR "H4". { iPureIntro.  unfold inflight in *. rewrite <- app_assoc. done.   }
            iLeft. done.
          }
          iApply "Hcont". iModIntro. iFrame.
          iDestruct "H1" as "[HPv _]". iFrame.
      replace  (length recv + 0%nat)  with (Z.of_nat (length recv)) by lia.
      done.
        }
        {
          iDestruct (big_sepL_cons with "H1") as "[HPv Hrest]".
          iMod ("Hinv_close" with "[HsentI Hoc Hrest H2 H4 Hcons_new]") as "H".
          {
            iNext. iFrame. iSplitR "H4 Hrest". { iPureIntro.  unfold inflight in *. rewrite <- app_assoc. done.   }
            iFrame.
          iApply (big_sepL_proper _ _ (v0 :: rest) with "Hrest").
intros k y z.
rewrite length_app.
rewrite singleton_length.
replace  ((length recv + 1)%nat + k)   with  (length recv + S k)  by lia.
done.
          }
          iApply "Hcont". iModIntro. iFrame.
      replace  (length recv + 0%nat)  with (Z.of_nat (length recv)) by lia.
      done.
        }
      }
      {
        destruct rest.
        {
          iMod ("Hinv_close" with "[HsentI Hoc H2 H5 Hcons_new]") as "H".
          {
            iNext. iFrame. iSplitR "H5". { iPureIntro.  unfold inflight in *. rewrite <- app_assoc. done.   }
            iRight. iFrame.
          }
          iApply "Hcont". iModIntro. iFrame.
          iDestruct "H1" as "[HPv _]". iFrame.
      replace  (length recv + 0%nat)  with (Z.of_nat (length recv)) by lia.
      done.
        }
        {
          iDestruct (big_sepL_cons with "H1") as "[HPv Hrest]".
          iMod ("Hinv_close" with "[HsentI Hoc Hrest H2 H5 Hcons_new]") as "H".
          {
            iNext. iFrame. iSplitR "H5 Hrest". { iPureIntro.  unfold inflight in *. rewrite <- app_assoc. done.   }
             iFrame.
          iApply (big_sepL_proper _ _ (v0 :: rest) with "Hrest").
intros k y z.
rewrite length_app.
rewrite singleton_length.
replace  ((length recv + 1)%nat + k)   with  (length recv + S k)  by lia.
done.
          }
          iApply "Hcont". iModIntro. iFrame.
      replace  (length recv + 0%nat)  with (Z.of_nat (length recv)) by lia.
      done.
        }
      }
    }
  }
Qed.

(** SPSC receive operation with history tracking *)
Lemma wp_spsc_receive γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                      (received : list V) :
  {{{ is_spsc γ ch P R ∗ spsc_consumer γ received }}}
    chan.receive t #ch
  {{{ (v:V) (ok:bool), RET (#v, #ok);
      (if ok then P (length received) v ∗ spsc_consumer γ (received ++ [v])
            else R received ∗ ⌜ v = (zero_val V) ⌝ )%I }}}.
Proof using All.
  iIntros (Φ) "(#Hspsc & Hcons) Hcont".

  (* Extract channel info from SPSC predicate *)
  iPoseProof "Hspsc" as "[#Hch _]".
  wp_apply (chan.wp_receive with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & _ & _)".
  iApply (spsc_rcv_au with "[$Hspsc] [$] [$Hcons]").
  iNext. iFrame.
Qed.

(** ** Send Operation *)

Lemma spsc_send_au γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                   (sent : list V) (v : V) Φ :
  is_spsc γ ch P R -∗
  £1 ∗ £1 ∗ £1 -∗
  spsc_producer γ sent ∗ P (length sent) v -∗
  ▷ (spsc_producer γ (sent ++ [v]) -∗ Φ) -∗
  send_au γ.(chan_name) v Φ.
Proof.
  iIntros "#Hspsc (Hlc1 & Hlc2 & Hlc3) [Hprod HP] Hcont".
  iDestruct "Hspsc" as "[Hchan Hinv]".

  (* Provide the send atomic update *)
  iMod (lc_fupd_elim_later with "Hlc1 Hcont") as "Hcont".

  (* Open the SPSC invariant to provide the atomic update *)
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc2 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".

  (* Establish agreement between our sent and invariant's sent *)
  iDestruct (dghost_var_agree with "Hprod HsentI") as %->.

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.

  (* Case analysis on channel state *)
  destruct s; try done.

  { (* Case: Buffered channel *)
    iIntros "Hoc".

    (* Update sent history *)
    iCombine "Hprod HsentI" as "Hsent_full".
    iMod (dghost_var_update (sent0 ++ [v]) with "Hsent_full") as "[HsentI_new Hprod_new]".

    (* Close invariant *)
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HsentI_new HrecvI Hinv_open HP]") as "_".
    {
      iNext. iExists (chanstate.Buffered (buff ++ [v])), (sent0 ++ [v]), recv.
      iFrame. simpl.
      subst sent0. iFrame. unfold inflight. rewrite length_app.
      replace (Z.of_nat (length recv + length buff))  with  (Z.of_nat (length recv) + Z.of_nat (length buff + 0)) by lia.
      iFrame. iPureIntro. rewrite app_assoc. done.
    }

    (* Apply continuation *)
    iModIntro. iApply "Hcont". unfold spsc_producer. iFrame.
  }

  { (* Case: Idle channel - need to wait for receiver *)
    iIntros "Hoc".

    (* Update sent history *)
    iCombine "Hprod HsentI" as "Hsent_full".
    iMod (dghost_var_update (sent0 ++ [v]) with "Hsent_full") as "[HsentI_new Hprod_new]".

    iMod "Hmask".
    iNamed "Hoc".
    iAssert (own_chan γ.(chan_name) V (chanstate.SndPending v))%I
      with "[Hchanrepfrag]" as "Hoc".
    { iFrame "∗#". iPureIntro. unfold chan_cap_valid. done. }

    (* Close invariant with SndPending state *)
    iMod ("Hinv_close" with "[Hoc HsentI_new HrecvI HP]") as "_".
    {
      iNext. iExists (chanstate.SndPending v), (sent0 ++ [v]), recv.
      iFrame.
      unfold inflight in Hrel. simpl in *. rewrite app_nil_r in Hrel.
      subst sent0. iFrame.
      iPureIntro. done.
    }

    (* Provide send_nested_au *)
    iModIntro. unfold send_nested_au.

    iInv "Hinv" as "Hinv_open2" "Hinv_close2".
    iMod (lc_fupd_elim_later with "[$] Hinv_open2") as "Hi".
    iNamed "Hi".
    iApply fupd_mask_intro; [solve_ndisj | iIntros "Hmask1"].
    iNext. iNamed "Hi". iFrame.
    iDestruct (dghost_var_agree with "Hprod_new HsentI") as %Heq.

    (* Case analysis on current state *)
    unfold chan_cap_valid in Hcapvalid.
    destruct s; try done.
    {
      (* RcvCommit case - complete handshake *)
      iIntros "Hoc".
      iMod "Hmask1".
      iMod ("Hinv_close2" with "[HsentI HrecvI Hoc]") as "_".
      {
        iNext. iExists chanstate.Idle, sent, recv0.
        iFrame.
        iPureIntro. rewrite Hrel0. simpl. done.
      }
      iModIntro. iApply "Hcont" in "Hprod_new". done.
    }
    {
      (* Closed channel - invalid (producer permission conflict) *)
      destruct drain.
      {
        iDestruct "Hi" as "(Hd & Hspp)".
        unfold spsc_producer.
        iCombine "HsentI Hd" as "Hfull".
        iExFalso.
        iDestruct (dghost_var_valid_2 with "Hfull Hprod_new") as "[%Hvalid _]".
        done.
      }
      {
        iDestruct "Hi" as "(Hd & Hspp & H3)".
        unfold spsc_producer.
        iCombine "HsentI Hspp" as "Hfull".
        iExFalso.
        iDestruct (dghost_var_valid_2 with "Hfull Hprod_new") as "[%Hvalid _]".
        done.
      }
    }
  }

  { (* Case: RcvPending - fast path completion *)
    iIntros "Hoc".

    (* Update sent history *)
    iCombine "Hprod HsentI" as "Hsent_full".
    iMod (dghost_var_update (sent0 ++ [v]) with "Hsent_full") as "[HsentI_new Hprod_new]".

    iMod "Hmask".

    (* Close invariant with SndCommit state *)
    iMod ("Hinv_close" with "[Hoc HsentI_new HrecvI HP]") as "_".
    {
      iNext. iExists (chanstate.SndCommit v), (sent0 ++ [v]), recv.
      iFrame.
      unfold inflight in Hrel. simpl in *. rewrite app_nil_r in Hrel.
      subst sent0. iFrame.
      iPureIntro. done.
    }

    (* Apply the final continuation *)
    iModIntro. iApply "Hcont".
    unfold spsc_producer. iFrame.
  }

  { (* Case: Closed channel - invalid (producer permission conflict) *)
    destruct drain.
    {
      iDestruct "Hinv_open" as "(Hd & Hspp)".
      unfold spsc_producer.
      iCombine "HsentI Hd" as "Hfull".
      iExFalso.
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]".
      done.
    }
    {
      iDestruct "Hinv_open" as "(Hd & Hspp & H3)".
      unfold spsc_producer.
      iCombine "HsentI Hspp" as "Hfull".
      iExFalso.
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]".
      done.
    }
  }
Qed.

(** SPSC send operation with history tracking *)
Lemma wp_spsc_send γ ch (P : Z -> V → iProp Σ) (R : list V → iProp Σ)
                   (sent : list V) (v : V) :
  {{{ is_spsc γ ch P R ∗ spsc_producer γ sent ∗ P (length sent) v }}}
    chan.send t #ch #v
  {{{ RET #(); spsc_producer γ (sent ++ [v]) }}}.
Proof using All.
  iIntros (Φ) "(#Hspsc & Hprod & HP) Hcont".

  (* Extract channel info from SPSC predicate *)
  unfold is_spsc.
  iPoseProof "Hspsc" as "[Hchan _]".

  (* Use wp_Send with our atomic update *)
  wp_apply (chan.wp_send ch v γ.(chan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & _)".

  iApply (spsc_send_au with "[$Hspsc] [$] [$Hprod $HP]").
  done.
Qed.

(** ** Close Operation *)

Lemma spsc_close_au γ ch P R sent Φ :
  is_spsc γ ch P R -∗
  £1 -∗
  spsc_producer γ sent ∗ R sent -∗
  ▷ Φ -∗
  close_au γ.(chan_name) V Φ.
Proof.
  iIntros "#Hspsc Hlc1 [Hprod HP] Hcont".
  iDestruct "Hspsc" as "[Hchan #Hinv]".

  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iDestruct (dghost_var_agree with "Hprod HsentI") as %->.

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.

  destruct s; try done.
  - (* Buffered *)
    iIntros "Hoc". iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI HP Hprod Hinv_open]") as "_".
    { iModIntro. iFrame. destruct buff; [iFrame|iFrame]; iPureIntro; done. }
    iModIntro. by iApply "Hcont".

  - (* Idle *)
    iIntros "Hoc". iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc HsentI HrecvI HP Hprod Hinv_open]") as "_".
    { iModIntro. iFrame. unfold spsc_producer. iFrame. iPureIntro. done. }
    iModIntro. by iApply "Hcont".

  - (* Closed *)
    destruct drain.
    + unfold spsc_producer. simpl.
      iDestruct "Hinv_open" as "[Hgv1 HR]".
      iCombine "HsentI HrecvI" as "H".
      iDestruct "H" as "[Hsent Hrecv]".
      iCombine "Hgv1 Hsent" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]". done.

    + unfold spsc_producer. simpl.
      iDestruct "Hinv_open" as "[Hgv1 HR]".
      iDestruct "HR" as "[Hgv2 HR]".
      iCombine "Hgv2 HsentI" as "Hfull".
      iDestruct (dghost_var_valid_2 with "Hfull Hprod") as "[%Hvalid _]". done.
Qed.

(** SPSC close operation *)
Lemma wp_spsc_close γ ch P R sent `[ct ↓u go.ChannelType dir t] :
  {{{  is_spsc γ ch P R ∗ spsc_producer γ sent ∗ R sent }}}
    #(functions go.close [ct]) #ch
  {{{ RET #(); True }}}.
Proof using All.
  iIntros (Φ) "( #Hspsc & Hprod & HP) Hcont".
  iPoseProof "Hspsc" as "[Hchan _]".
  iApply (chan.wp_close with "Hchan").
  iIntros "(Hlc1 & _ & _ & _)".
  iApply (spsc_close_au with "[$Hspsc] [$] [$Hprod $HP]").
  iModIntro.
  by iApply "Hcont".
Qed.

End spsc.
