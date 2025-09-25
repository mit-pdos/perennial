
Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_send chan_au_recv chan_au_base chan_init.

Section simple_mess_pass.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Implicit Types (s : chan_rep.t V).

(*------------------------------------------------------------------------------
   Simple message-passing protocol
  This module provides a tiny protocol where every in-flight value on a channel satisfies a 
  caller-supplied predicate [P]. The protocol is intentionally minimal.
   Naming note: we use "mess_pass" (message passing) instead of "mp" to avoid
   confusion with "multi-producer".
  -----------------------------------------------------------------------------*)
Definition is_simple_mess_pass γ (ch : loc) P cap : iProp Σ :=
  is_channel ch cap γ  ∗
  inv nroot (
      ∃ s,
        "Hch" ∷ own_channel ch s cap γ ∗
    (match s with
     | chan_rep.Idle =>
        True
     | chan_rep.SndWait v | chan_rep.SndDone v =>
         P v
     | chan_rep.Buffered buff => 
        [∗ list] v ∈ buff, P v
     | chan_rep.RcvWait | chan_rep.RcvDone =>
         True
     (* We don't close in this protocol. *)
     | chan_rep.Closed _ => False
     end
    )).

Lemma start_simple_mess_pass P ch s cap γ:
  is_channel ch cap γ  -∗
  own_channel ch chan_rep.Idle cap γ ={⊤}=∗
  is_simple_mess_pass γ ch P cap.
Proof.
  intros.
  iIntros "#? Hchan".
  iFrame "#". iFrame. simpl.
  iApply inv_alloc.
  iExists chan_rep.Idle.
  iFrame "∗%#".
Qed.

Lemma wp_simple_mess_pass_receive γ ch P cap:
  {{{
      is_pkg_init channel ∗
      is_simple_mess_pass γ ch P cap
  }}}
    ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #()
  {{{
      v,RET (#v, #true); P v
  }}}.
Proof.
Admitted. 

Lemma wp_simple_mess_pass_send γ ch v P cap :
  {{{
      is_pkg_init channel ∗
      is_simple_mess_pass γ ch P cap ∗ 
      P v
  }}}
    ch @ (ptrT.id channel.Channel.id) @ "Send" #t #()
  {{{
      RET (#()); True
  }}}.
Proof.
Admitted.

End simple_mess_pass.
