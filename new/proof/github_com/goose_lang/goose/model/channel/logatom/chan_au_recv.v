From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
From New.proof Require Import proof_prelude.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

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
  is_channel ch cap γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s cap γ ∗
    (match s with
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
              | _ => own_channel ch s' 0 γ ={∅,⊤}=∗ Φnotready (* Offer rescinded/no progress *)
              end))
     | chan_rep.Closed draining =>
         own_channel ch (chan_rep.Closed draining) cap γ ={∅,⊤}=∗ Φsuccess (default_val V) false
     | _ => (* busy with other exchange *)
         own_channel ch s 0 γ ={∅,⊤}=∗ Φnotready
     end).

(* ================ GENERIC CHANNEL SPECS ================ *)

(* chan_blocking_receive_atomic_update models the logical behavior of a Go blocking receive.
   It handles buffered, unbuffered, and closed channels in a single, comprehensive specification.
   The core of the logic is a match on the channel's state, delegating to the correct
   sub-specification for each case. *)
Definition chan_blocking_receive_atomic_update ch (cap: w64) (γ: chan_names) (Φsuccess : V → bool → iProp Σ) : iProp Σ :=
  is_channel ch cap γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s cap γ ∗
    (match s with
    (* Case: Buffered channel with at least one value. *)
    | chan_rep.Buffered (fr :: rest) =>
        own_channel ch (chan_rep.Buffered rest) cap γ ={∅,⊤}=∗ Φsuccess fr true
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
                    (* Other states won't happen on success through this path but client shouldn't have to prove that *)
                    | _ =>
                       True
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
    | _ => True
    end).

(* chan_nonblocking_receive_atomic_update models the logical behavior of a Go non-blocking receive.
   It handles all cases: buffered, unbuffered, and closed. Unlike the blocking version, it fails
   if the condition for success is not met immediately. *)
Definition chan_nonblocking_receive_atomic_update ch (cap: w64) (γ: chan_names) (Φsuccess : V → bool → iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
  is_channel ch cap γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s cap γ ∗
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

(* wp_Receive is the main lemma that links the logical specification to the concrete Go code.
   It states that for any postcondition Φ, if you have the proper preconditions,
   the Go "Receive" method will terminate and satisfy the atomic update specified. *)
Lemma wp_Receive (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_blocking_receive_atomic_update ch cap γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #() {{ Φ }}.
Proof.
Admitted.

(* This lemma proves that the `TryReceive(true)` Go function call satisfies
   the `chan_try_blocking_receive_atomic_update` specification.
   The postcondition `Φ` must handle all three possible return values from `TryReceive`:
   `(selected, value, ok)`. *)
Lemma wp_TryReceive_blocking (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_try_blocking_receive_atomic_update ch cap γ (λ v ok, Φ (#true, #v, #ok)%V) (Φ (#false, #(default_val V), #true)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TryReceive" #true #t #() {{ Φ }}.
Proof.
Admitted.

(* This lemma proves that the `TryReceive(false)` Go function call satisfies
   the `chan_nonblocking_receive_atomic_update` specification.
   The postcondition `Φ` must handle all three possible return values from `TryReceive`:
   `(selected, value, ok)`. *)
Lemma wp_TryReceive_nonblocking (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_nonblocking_receive_atomic_update ch cap γ (λ v ok, Φ (#true, #v, #ok)%V) (Φ (#false, #(default_val V), #true)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "TryReceive" #false #t #() {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
