From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base.
From New.proof Require Import proof_prelude.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

Section atomic_specs.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!goGlobalsGS Σ}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Local Notation deps := (ltac2:(build_pkg_init_deps 'channel) : iProp Σ) (only parsing).
#[global] Program Instance : IsPkgInit channel :=
  {|
    is_pkg_init_def := True;
    is_pkg_init_deps := deps;
  |}.

(* Used for a standalone send as well as a send case in a blocking select statement. 
   This tracks the possible success paths for both unbuffered and buffered channels.
*)
Definition chan_blocking_send_atomic_update ch (v : V) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    (match s with
    (* Case: Buffered channel with available capacity, enqueue the value. *)
    | chan_rep.Buffered buff cap =>
      if decide (length buff < cap) then
        (* Space available: enqueue the value *)
        own_channel ch (chan_rep.Buffered (buff ++ [v]) cap) γ ={∅,⊤}=∗ Φ
      else
        (* Buffer full: not applicable for blocking send when it succeeds *)
        False
    (* Case: Unbuffered channel with waiting receiver, complete the exchange. *)
    | chan_rep.RcvWait =>
          own_channel ch (chan_rep.SndDone v) γ ={∅,⊤}=∗ Φ
    (* Case: Unbuffered idle channel. This requires a two-phase handshake. *)
    | chan_rep.Idle =>
          (* Register as a waiting sender *)
          own_channel ch (chan_rep.SndWait v) γ ={∅,⊤}=∗
               |={⊤,∅}=> ▷∃ s', own_channel ch s' γ ∗
                 (match s' with
                    (* If we succeed through this path, the receiver completed the offer *)
                    | chan_rep.RcvDone =>
                        own_channel ch chan_rep.Idle γ ={∅,⊤}=∗ Φ
                    | _ => False
                 end)
    | _ => False
    end).

(* Used for an attempt at sending that is part of a nonblocking select statement. *)
Definition chan_nonblocking_send_atomic_update ch (v : V) (γ: chan_names) (Φsuccess : iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    match s with
    (* Case: Buffered channel. If the buffer is full, the send fails. *)
    | chan_rep.Buffered buff cap =>
         if decide (length buff < cap) then
           (* Success path: add to buffer *)
           (own_channel ch (chan_rep.Buffered (buff ++ [v]) cap) γ ={∅,⊤}=∗ Φsuccess)
         else
           (* Buffer full, not selectable *)
           (own_channel ch s γ ={∅,⊤}=∗ Φnotready)
    (* Case: Unbuffered channel. Succeeds only if there's a waiting receiver. *)
    | chan_rep.RcvWait =>
         own_channel ch (chan_rep.SndDone v) γ ={∅,⊤}=∗ Φsuccess
    (* Case: Channel is closed. *)
    | chan_rep.Closed _ _ =>
         False (* Send on closed channel - should panic *)
    (* Case: Unbuffered channel without a waiting receiver. The send fails immediately. *)
    | _ =>
        own_channel ch s γ ={∅,⊤}=∗ Φnotready
    end.

(* This is used for the offer-based try loop used for blocking select statements.
   It should not be used directly by clients and will only be used to prove the blocking send update
   via Lob induction. *)
Definition unbuffered_try_blocking_send_atomic_update
  (ch: loc) (v: V) (γ: chan_names)
  (Φsuccess: iProp Σ) (Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    (match s with
     (* Immediate success, a receiver is waiting and we complete the exchange *)
     | chan_rep.RcvWait =>
         own_channel ch (chan_rep.SndDone v) γ ={∅,⊤}=∗ Φsuccess
     (* No exchange in progress, make an offer to receivers. *)
     | chan_rep.Idle =>
        own_channel ch (chan_rep.SndWait v) γ ={∅,⊤}=∗
           |={⊤,∅}=> ▷(
             ∃ s', own_channel ch s' γ ∗
             (match s' with
               (* Offer accepted by a receiver, reset the channel and take success continuation *)
              | chan_rep.RcvDone => 
                  own_channel ch chan_rep.Idle γ ={∅,⊤}=∗ Φsuccess
               (* Offer rescinded. *)
              | chan_rep.SndWait v => own_channel ch s' γ ={∅,⊤}=∗ Φfailure 
               (* No other state transitions are legal while an offer is in progress, including close *)
              | _ => 
                  False 
              end))
    (* Exchange in progress *)
     | chan_rep.SndWait _ | chan_rep.RcvDone | chan_rep.SndDone _ => 
         own_channel ch s γ ={∅,⊤}=∗ Φfailure
     (* Closed panics on send and this offer logic does not apply to buffered channels. *)
     | _ => False
     end).

(* ================ MAIN LEMMAS ================ *)

Lemma wp_Send (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch γ -∗
  ▷(chan_blocking_send_atomic_update ch v γ (Φ #())) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_TrySend_blocking (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch γ -∗
  ▷(unbuffered_try_blocking_send_atomic_update ch v γ (Φ (#true)) (Φ (#false))) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TrySend" #true #t #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_TrySend_nonblocking (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch γ -∗
  ▷(chan_nonblocking_send_atomic_update ch v γ (Φ (#true)) (Φ (#false))) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TrySend" #false #t #v {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
