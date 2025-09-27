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

Lemma wp_TrySend (ch: loc) (cap: Z) (v: V) (γ: chan_names) (P: iProp Σ):
  ∀ Φ (b: bool),
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (* P is here to support helping within a select statement. This is because the internal choice of 
  which case's atomic update cannot be made prematurely if an offer isn't accepted, so we need to 
  store the whole collective conjunct of atomic updates in the channel mutex invariant for the 
  channel we are making an offer on. *)
  P ∗ (P -∗ ((send_au_fast ch cap v γ (Φ (#true))))) -∗ 
  (* Keep resources for attempts at this and/or other ops *)
  (P -∗ (Φ (#false))) -∗ 
  WP ch @ (ptrT.id channel.Channel.id) @ "TrySend" #t #v #true {{ Φ }}.
Proof.
Admitted.

Lemma wp_TrySend_nb (ch: loc) (cap: Z) (v: V) (γ: chan_names) (P: iProp Σ):
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (* P is here to support helping within a select statement. This is because the internal choice of 
  which case's atomic update cannot be made prematurely if an offer isn't accepted, so we need to 
  store the whole collective conjunct of atomic updates in the channel mutex invariant for the 
  channel we are making an offer on. *)
  P ∗ (P -∗ ((send_au_slow ch cap v γ (Φ (#true))))) -∗ 
  (* Keep resources for attempts at this and/or other ops *)
  (P -∗ (Φ (#false))) -∗ 
  WP ch @ (ptrT.id channel.Channel.id) @ "TrySend" #t #v #false {{ Φ }}.
Proof.
Admitted.

Lemma wp_Send (ch: loc) (cap: Z) (v: V) (γ: chan_names):
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch cap γ -∗
  (send_au_slow ch cap v γ (Φ #())) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
