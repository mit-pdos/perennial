Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
From New.golang.theory Require Import chan.

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

Lemma future_is_channel γfuture ch P :
  is_future γfuture ch P ⊢ is_channel ch 1 γfuture.(future.chan_name).
Proof.
  iDestruct 1 as "[$ _]".
Qed.

(** ** Fulfill Operation (Send) *)

Lemma future_fulfill_au γ ch (P : V → iProp Σ) (v : V) :
  ∀ (Φ: iProp Σ),
  is_future γ ch P -∗
  £1 ∗ fulfill_token γ ∗ P v -∗
  ▷ (True -∗ Φ) -∗
  send_au_slow ch 1 v γ.(chan_name) Φ.
Proof.
  iIntros (Φ) "#Hfuture (Hlc & Hfulfillt & HP) Hcont".
  unfold is_future.
  iDestruct "Hfuture" as "[#Hchan #Hinv]".

  unfold send_au_slow.
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iDestruct "Hlc" as "[Hlc1 Hrest]".
  iMod (lc_fupd_elim_later with "[$] [$Hinv_open]") as "Hinv_open".
  iNamed "Hinv_open".

  iDestruct (ghost_var_agree with "Hfulfill Hfulfillt") as %Hagree.

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iExists s. iFrame "Hch".

  destruct s; try done.
  destruct buff as [|v_buf rest].
{
  
  iDestruct "Hinv_open" as %Hdisj.
  destruct Hdisj as [[Hawait_eq Hfulfill_eq] | [Hawait_eq Hfulfill_eq]]; subst.
  - (* Initial state - can fulfill *)
    simpl.
    iIntros "Hoc".
    iMod "Hmask".
    iCombine "Hfulfill Hfulfillt" as "Hfulfill_full".
    iMod (ghost_var_update false with "Hfulfill_full") as "[HfulfillI_new _]".
    iMod ("Hinv_close" with "[Hoc Hawait HP HfulfillI_new]") as "_".
    {
      iNext. iExists (chan_rep.Buffered [v]), true, false.
      iFrame. iPureIntro. split; done.
    }
    iModIntro. iApply "Hcont".
    done.
  - (* Final state - should not happen *)
    iExFalso. done.
    }
    {
      destruct rest. all: done.
    }
Qed.

Lemma wp_future_fulfill γ ch (P : V → iProp Σ) (v : V) :
  {{{ is_future γ ch P ∗ fulfill_token γ ∗ P v }}}
    chan.send #t #ch #v
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hfuture & Hfulfillt & HP) Hcont".

  unfold is_future.
  iDestruct "Hfuture" as "[#Hchan #Hiv]".

  wp_apply (chan.wp_send ch 1 v γ.(chan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".

  iApply (future_fulfill_au with "[$Hiv $Hchan] [$]").
  done.
Qed.

Lemma future_await_au γ ch (P : V → iProp Σ) :
  ∀ (Φ: V → bool → iProp Σ),
  is_future γ ch P -∗
  £1 ∗ await_token γ -∗
  ▷ (∀ v, P v -∗ Φ v true) -∗
  rcv_au_slow ch 1 γ.(chan_name) (λ (v:V) (ok:bool), Φ v ok).
Proof.
  iIntros (Φ) "#Hfuture [Hlc Hawaitt] HΦcont".
  unfold is_future.
  iDestruct "Hfuture" as "[_ Hinv]".

  unfold rcv_au_slow.
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iDestruct "Hlc" as "[Hlc1 Hrest]".
  iMod (lc_fupd_elim_later with "[$] [$Hinv_open]") as "Hinv_open".
  iNamed "Hinv_open".

  iDestruct (ghost_var_agree with "Hawait Hawaitt") as %Hagree.

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iExists s. iFrame "Hch".

  destruct s; try done.
  destruct buff as [|v [|? ?]]; try done.

  (* Value in buffer - can await *)
  iDestruct "Hinv_open" as "[%Hstates HP]".
  destruct Hstates as [Hawait_eq Hfulfill_eq]; subst.
  iIntros "Hoc".
  iMod "Hmask".
  iCombine "Hawait Hawaitt" as "Hawait_full".
  iMod (ghost_var_update false with "Hawait_full") as "[HawaitI_new _]".
  iMod ("Hinv_close" with "[Hoc HawaitI_new Hfulfill]") as "_".
  {
    iNext. iExists (chan_rep.Buffered []), false, false.
    iFrame. iPureIntro. right. split; done.
  }
  iModIntro. iApply "HΦcont". done.
Qed.

(** Future await operation - consumes await token to receive value and P(v) *)
Lemma wp_future_await γ ch (P : V → iProp Σ) :
  {{{ is_future γ ch P ∗ await_token γ }}}
    chan.receive #t #ch
  {{{ (v : V), RET (#v, #true); P v }}}.
Proof.
  iIntros (Φ) "(#Hfuture & Hawaitt) Hcont".

  unfold is_future.
  iDestruct "Hfuture" as "[#Hchan #Hinv]".
  
  iApply (chan.wp_receive ch 1 γ.(chan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2)".

  iApply ((future_await_au γ ch  P ) with "[$Hchan $Hinv] [$] [Hcont]").
  iNext. iFrame.
Qed.

End future.
