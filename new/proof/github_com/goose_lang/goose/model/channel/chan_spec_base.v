From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_ghost_state big_sep_seq chan_init.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose.model
  Require Export channel.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.  
Context  `{!chanGhostStateG Σ}.

(* Define valid states as an inductive type *)
Inductive valid_chan_state := 
  | Valid_start
  | Valid_receiver_ready
  | Valid_sender_ready
  | Valid_receiver_done
  | Valid_sender_done
  | Valid_closed.

(* Define equality comparison for valid_chan_state *)
Definition valid_chan_state_eq (vs1 vs2: valid_chan_state) : bool :=
  match vs1, vs2 with
  | Valid_start, Valid_start => true
  | Valid_receiver_ready, Valid_receiver_ready => true
  | Valid_sender_ready, Valid_sender_ready => true
  | Valid_receiver_done, Valid_receiver_done => true
  | Valid_sender_done, Valid_sender_done => true
  | Valid_closed, Valid_closed => true
  | _, _ => false
  end.

(* Notation for equality *)
Notation "vs1 =?= vs2" := (valid_chan_state_eq vs1 vs2) (at level 70).


(* Define word constants to match Go implementation *)
Definition CS_START_W : w64 := W64 0.
Definition CS_RECEIVER_READY_W : w64 := W64 1.
Definition CS_SENDER_READY_W : w64 := W64 2.
Definition CS_RECEIVER_DONE_W : w64 := W64 3.
Definition CS_SENDER_DONE_W : w64 := W64 4.
Definition CS_CLOSED_W : w64 := W64 5.

(* Conversion function from valid state to word representation *)
Definition valid_to_word (vs: valid_chan_state) : w64 := 
  match vs with
    | Valid_start => CS_START_W
    | Valid_receiver_ready => CS_RECEIVER_READY_W
    | Valid_sender_ready => CS_SENDER_READY_W
    | Valid_receiver_done => CS_RECEIVER_DONE_W
    | Valid_sender_done => CS_SENDER_DONE_W
    | Valid_closed => CS_CLOSED_W
  end.

(* Define word constants for offer results to match Go implementation *)
Definition OFFER_RESCINDED_W : w64 := W64 0.
Definition COMPLETED_EXCHANGE_W : w64 := W64 1.
Definition CLOSE_INTERRUPTED_OFFER_W : w64 := W64 2.

(* Define result type for better type safety and readability *)
Inductive rescind_result := 
  | OfferRescinded
  | CompletedExchange
  | CloseInterruptedOffer.

(* Conversion function from result type to word representation *)
Definition rescind_to_word (res: rescind_result) : w64 := 
  match res with
    | OfferRescinded => OFFER_RESCINDED_W
    | CompletedExchange => COMPLETED_EXCHANGE_W
    | CloseInterruptedOffer => CLOSE_INTERRUPTED_OFFER_W
  end.


(* Helper function to check if a word corresponds to a valid channel state *)
Definition is_valid_cs_word (w: w64) : bool :=
  match word.unsigned w with
  | 0%Z | 1%Z | 2%Z | 3%Z | 4%Z | 5%Z => true
  | _ => false
  end.

(* Semantic model of a Select case's direction *)
Inductive select_dir :=
  | SelectSend
  | SelectRecv.

(* Word constants to match Go runtime encoding *)
Definition SELECT_SEND_W : w64 := W64 0.
Definition SELECT_RECV_W : w64 := W64 1.

(* Convert select_dir to word encoding *)
Definition select_dir_to_word (d: select_dir) : w64 :=
  match d with
  | SelectSend => SELECT_SEND_W
  | SelectRecv => SELECT_RECV_W
  end.

(* Equality function for select_dir *)
Definition select_dir_eq (d1 d2: select_dir) : bool :=
  match d1, d2 with
  | SelectSend, SelectSend => true
  | SelectRecv, SelectRecv => true
  | _, _ => false
  end.

Lemma valid_states_eq_dec : forall (vs1 vs2 : valid_chan_state),
  {vs1 = vs2} + {vs1 ≠ vs2}.
Proof.
  decide equality.
Qed.

Definition send_ctr_frozen (vs: valid_chan_state): bool :=
  match vs with 
    | Valid_closed => true
    | _ => false
  end.

Definition recv_ctr_frozen (vs: valid_chan_state) (send_count recv_count: nat): bool :=
  match vs with
    | Valid_closed => (send_count =? recv_count)
    | _ => false
  end.

End proof.

