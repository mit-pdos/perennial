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
Definition chan_send_atomic_update ch (cap: w64) (v : V) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
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
        True
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
                    | _ => True
                 end)
    | chan_rep.SndWait _ | chan_rep.RcvDone | chan_rep.SndDone _ =>  True
    | chan_rep.Closed _ => False
    end).

Lemma wp_TrySend (ch: loc) (cap: w64) (v: V) (γ: chan_names) (P: iProp Σ):
  ∀ Φ (b: bool),
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (* P is here to support helping within a select statement. This is because the internal choice of 
  which case's atomic update cannot be made prematurely if an offer isn't accepted, so we need to 
  store the whole collective conjunct of atomic updates in the channel mutex invariant for the 
  channel we are making an offer on. *)
  P ∗ (P -∗ (▷(chan_send_atomic_update ch cap v γ (Φ (#true))))) -∗ 
  (* Keep resources for attempts at this and/or other ops *)
  (P -∗ (Φ (#false))) -∗ 
  WP ch @ (ptrT.id channel.Channel.id) @ "TrySend" #t #v #b {{ Φ }}.
Proof.
Admitted.

Lemma wp_Send (ch: loc) (cap: w64) (v: V) (γ: chan_names):
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  ▷(chan_send_atomic_update ch cap v γ (Φ #())) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
