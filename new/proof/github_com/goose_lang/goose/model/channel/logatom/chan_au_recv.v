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

Definition chan_receive_atomic_update ch (cap: w64) (γ: chan_names) (Φsuccess : V → bool → iProp Σ) : iProp Σ :=
   "#Hperschan" ∷ is_channel ch cap γ ∗
   "Hlogatom" ∷ |={⊤,∅}=>
    ▷∃ s,  "Hoc" ∷  own_channel ch s cap γ ∗
    (match s with
    (* Case: Buffered channel with at least one value. *)
    | chan_rep.Buffered (fr :: rest) =>
        own_channel ch (chan_rep.Buffered rest) cap γ ={∅,⊤}=∗ Φsuccess fr true
    (* Case: Buffered channel with no values, N/A for success. *)
    | chan_rep.Buffered [] => True
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
                    | _ => True
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

Lemma wp_Receive (ch: loc) (cap: w64) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_receive_atomic_update ch cap γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #() {{ Φ }}.
Proof.
Admitted.

Lemma wp_TryReceive (ch: loc) (cap: w64) (γ: chan_names) (P: iProp Σ) :
  ∀ Φ (b: bool),
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (* P is here to support helping within a select statement. This is because the internal choice of 
  which case's atomic update cannot be made prematurely if an offer isn't accepted, so we need to 
  store the whole collective conjunct of atomic updates in the channel mutex invariant for the 
  channel we are making an offer on. *)
  P ∗ (P -∗ ▷(chan_receive_atomic_update ch cap γ (λ v ok, Φ (#true, #v, #ok)%V))) -∗
  (* Keep resources for attempts at this and/or other ops *)
  (P -∗ (Φ (#false, #(default_val V), #true)%V)) -∗ 
  WP ch @ (ptrT.id channel.Channel.id) @ "TryReceive" #t #b {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
