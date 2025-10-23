Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_send chan_au_recv chan_au_base chan_init.

(** * Future Channel Verification

    This file provides a high-level abstraction for future channels built on top
    of the low-level channel verification. A future represents a one-shot communication
    pattern where exactly one value is sent (fulfill) and exactly one value is
    received (await).

    Key features:
    - Exactly one fulfill operation allowed per future
    - Exactly one await operation allowed per future
    - Uses buffered channel with capacity 1
    - Ghost state tracks whether fulfill/await tokens have been consumed
    - Close operations are banned 
*)

Section future.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!ghost_varG Σ bool}.

(** ** Ghost State Names *)

Record future_names := {
  chan_name : chan_names;      (* Underlying channel ghost state *)
  await_name : gname;          (* One-shot await token *)
  fulfill_name : gname         (* One-shot fulfill token *)
}.

Notation half := (1/2)%Qp.

(** ** One-shot Token Predicates *)

(** Await token - permission to receive exactly once *)
Definition await_token (γ : future_names) : iProp Σ :=
  ghost_var γ.(await_name) half true.

(** Fulfill token - permission to send exactly once *)
Definition fulfill_token (γ : future_names) : iProp Σ :=
  ghost_var γ.(fulfill_name) half true.

(** ** Future Channel Invariant *)

(** The main Future channel predicate.

    Parameters:
    - P: Resource associated with the value (travels from fulfill to await)

    The invariant maintains:
    - Channel has capacity exactly 1 (buffered)
    - Empty buffer: both await and fulfill tokens available
    - Buffer with one value: fulfill token consumed, await token available, P(v) holds
    - Close operations are forbidden
    - After await: both tokens consumed, buffer empty
*)
Definition is_future (γ : future_names) (ch : loc)
                     (P : V → iProp Σ) : iProp Σ :=
  is_channel ch 1 γ.(chan_name) ∗
  inv nroot (
    ∃ s await_avail fulfill_avail,
      "Hch" ∷ own_channel ch 1 s γ.(chan_name) ∗
      "Hawait" ∷ ghost_var γ.(await_name) half await_avail ∗
      "Hfulfill" ∷ ghost_var γ.(fulfill_name) half fulfill_avail ∗
      (match s with
      (* Empty buffer: either initial state or final state *)
      | chan_rep.Buffered [] =>
          ⌜(await_avail = true ∧ fulfill_avail = true) ∨
           (await_avail = false ∧ fulfill_avail = false)⌝
      (* Fulfilled state: value in buffer, only await token available *)
      | chan_rep.Buffered [v] =>
          ⌜await_avail = true ∧ fulfill_avail = false⌝ ∗ P v
      (* No unbuffered or closing allowed *)
      | _ => False
      end)
  )%I.

(** ** Initialization *)

(** Create a Future channel from a capacity-1 buffered channel *)
Lemma start_future ch (P : V → iProp Σ) γ :
  is_channel ch 1 γ -∗
  (own_channel ch 1 (chan_rep.Buffered []) γ) ={⊤}=∗
  (∃ γfuture, is_future γfuture ch P ∗ await_token γfuture ∗ fulfill_token γfuture).
Proof.
  iIntros "#Hch Hoc".

  (* Allocate ghost variables for await and fulfill tokens *)
  iMod (ghost_var_alloc true) as (γawait) "[HawaitA HawaitF]".
  iMod (ghost_var_alloc true) as (γfulfill) "[HfulfillA HfulfillF]".

  (* Create the future_names record *)
  set (γfuture := {| chan_name := γ; await_name := γawait; fulfill_name := γfulfill |}).

  (* Allocate the invariant *)
  iMod (inv_alloc nroot _ (
    ∃ s await_avail fulfill_avail,
      "Hch" ∷ own_channel ch 1 s γ ∗
      "Hawait" ∷ ghost_var γawait half await_avail ∗
      "Hfulfill" ∷ ghost_var γfulfill half fulfill_avail ∗
      (match s with
       | chan_rep.Buffered [] =>
           ⌜(await_avail = true ∧ fulfill_avail = true) ∨
            (await_avail = false ∧ fulfill_avail = false)⌝
       | chan_rep.Buffered [v] =>
           ⌜await_avail = true ∧ fulfill_avail = false⌝ ∗ P v
       | _ =>
           False
       end)
  ) with "[Hoc HawaitA HfulfillA]") as "#Hinv".
  {
    (* Prove the invariant holds initially *)
    iNext. iExists (chan_rep.Buffered []), true, true. iFrame.
    iPureIntro. left. split; done.
  }

  (* Construct the final result *)
  iModIntro. iExists γfuture.
  unfold is_future, await_token, fulfill_token.
  iFrame "#". iFrame.
Qed.

(** ** Fulfill Operation (Send) *)

(** Future fulfill operation - consumes fulfill token and P(v) to send value *)
Lemma wp_future_fulfill γ ch (P : V → iProp Σ) (v : V) :
  {{{ is_pkg_init channel ∗ is_future γ ch P ∗ fulfill_token γ ∗ P v }}}
    ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hinit & #Hfuture & Hfulfillt & HP) Hcont".

  (* Extract channel info from Future predicate *)
  unfold is_future.
  iDestruct "Hfuture" as "[Hchan Hinv]".

  wp_apply (wp_Send ch 1 v γ.(chan_name) with "[$Hinit $Hchan]").
  iIntros "(? & ? & ? & ?)".

  (* Open the Future invariant to provide the atomic update *)
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".

  (* Establish agreement between our fulfill token and invariant's fulfill state *)
  iDestruct (ghost_var_agree with "Hfulfill Hfulfillt") as %Hagree.

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.

  (* Case analysis on channel state *)
  destruct s; try done.

  { (* Case: Buffered channel *)
    destruct buff as [|v_buf rest].
    { (* Empty buffer - this is the expected case *)
      iDestruct "Hinv_open" as %Hdisj.
      destruct Hdisj as [[Hawait Hfulfill_state] | [Hawait Hfulfill_state]].
      { (* Initial state case *)
        subst await_avail fulfill_avail.

        iIntros "Hoc".

        (* Update fulfill token to false (consumed) *)
        iCombine "Hfulfill Hfulfillt" as "Hfulfill_full".
        iMod (ghost_var_update false with "Hfulfill_full") as "[HfulfillI_new _]".

        (* Close invariant with value in buffer *)
        iMod "Hmask".
        iMod ("Hinv_close" with "[Hoc Hawait HfulfillI_new HP]") as "_".
        {
          iNext. iExists (chan_rep.Buffered [v]), true, false.
          iFrame.
          iPureIntro. split; done.
        }

        (* Apply continuation *)
        iModIntro. iApply "Hcont". done.
      }
      { (* Final state case - both tokens already consumed, should not happen *)
        subst await_avail fulfill_avail.
        iExFalso. done.
      }
    }
    { (* Non-empty buffer - should not happen with proper usage *)
      destruct rest. all: done.
    }
  }

Qed.

(** ** Await Operation (Receive) *)

(** Future await operation - consumes await token to receive value and P(v) *)
Lemma wp_future_await γ ch (P : V → iProp Σ) :
  {{{ is_pkg_init channel ∗ is_future γ ch P ∗ await_token γ }}}
    ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #()
  {{{ (v : V) , RET (#v, #true);
      P v }}}.
Proof.
  iIntros (Φ) "(#Hinit & #Hfuture & HawaitI) Hcont".

  (* Extract channel info from Future predicate *)
  unfold is_future.
  iDestruct "Hfuture" as "[Hchan Hinv]".

  (* Use wp_Receive with our atomic update *)
  iApply (wp_Receive ch 1 γ.(chan_name) with "[$Hinit $Hchan]").
  iIntros "(Hlc1 & _)".

  (* Open the Future invariant to provide the atomic update *)
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".

  (* Establish agreement between our await token and invariant's await state *)
  iDestruct (ghost_var_agree with "HawaitI Hawait") as %Hagree.

  (* Provide rcv_au_slow *)
  unfold rcv_au_slow.
  iExists s. iFrame "Hch".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame.

  (* Case analysis on channel state *)
  destruct s; try done.

  { (* Case: Buffered channel *)
    destruct buff as [|v rest].
    { (* Empty buffer - await must wait for fulfill *)
      iDestruct "Hinv_open" as %Hdisj.
      destruct Hdisj as [[Hawait_state Hfulfill_state] | [Hawait_state Hfulfill_state]].
      { (* Initial state case *)
        subst await_avail fulfill_avail.
        (* With await_avail = true, we should not be able to receive yet *)
        done.
      }
      { (* Final state case - both tokens consumed, should not happen *)
        subst await_avail fulfill_avail.
        (* This contradicts having the await token *)
        iExFalso. done.
      }
    }
    { (* Non-empty buffer - this is the expected case after fulfill *)
      destruct rest.
      { (* Exactly one value - expected case *)
        iDestruct "Hinv_open" as "[%Hstates HPv]".
        destruct Hstates as [Hawait_state Hfulfill_state].
        subst await_avail fulfill_avail.

        iIntros "Hoc".

        (* Update await token to false (consumed) *)
        iCombine "Hawait HawaitI" as "Hawait_full".
        iMod (ghost_var_update false with "Hawait_full") as "[HawaitI_new _]".

        (* Close invariant with empty buffer and both tokens consumed *)
        iMod "Hmask".
        iMod ("Hinv_close" with "[Hoc HawaitI_new Hfulfill]") as "_".
        {
          iNext. iExists (chan_rep.Buffered []), false, false.
          iFrame "Hoc HawaitI_new Hfulfill".
          iPureIntro. right. split; done.
        }

        (* Apply continuation with the value and its resource *)
        iModIntro. iApply "Hcont". iFrame.
      }
      { (* More than one value - impossible with capacity 1 *)
        iDestruct "Hinv_open" as "HFalse".
        iExFalso. done.
      }
    }
  }
Qed.

Lemma wp_future_await_discard_ok γ ch (P : V → iProp Σ) :
  {{{ is_pkg_init channel ∗ is_future γ ch P ∗ await_token γ }}}
    ch @ (ptrT.id channel.Channel.id) @ "ReceiveDiscardOk" #t #()
  {{{ (v : V) , RET #v;
      P v }}}.
Proof.
  wp_start. wp_auto.
  wp_apply ((wp_future_await γ ch P) with "[- HΦ return_val]").
  {
   iFrame.
  }
  iIntros (v).
  iIntros "HP".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End future.
