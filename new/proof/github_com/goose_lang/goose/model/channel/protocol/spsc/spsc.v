Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_send chan_au_recv chan_au_base chan_init.

Section spsc.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!ghost_varG Σ (list V)}.

Record spsc_names := {
  chan_name : chan_names;
  spsc_sent_name : gname;  
  spsc_recv_name : gname  
}.

Notation half := (1/2)%Qp.

(* Producer and consumer maintain half permission of the history of values sent/received respectively *)
Definition spsc_producer (γ:spsc_names) (sent:list V) : iProp Σ :=
    ghost_var γ.(spsc_sent_name) half sent.
Definition spsc_consumer (γ:spsc_names) (received:list V) : iProp Σ :=
    ghost_var γ.(spsc_recv_name) half received.

(* in-flight items that have not yet been received *)
Definition inflight (s : chan_rep.t V) : list V :=
  match s with
  | chan_rep.Buffered buff => buff
  | chan_rep.SndWait v | chan_rep.SndDone v => [v]
  | chan_rep.Closed draining => draining
  | _ => []
  end.

Definition is_spsc (γ:spsc_names) (ch:loc) 
                   (P: V → iProp Σ) (R: list V → iProp Σ) : iProp Σ :=
  ∃ (cap:w64) ,
    is_channel ch cap γ.(chan_name) ∗
    inv nroot (
      ∃ s sent recv,
        "Hch"    ∷ own_channel ch s cap γ.(chan_name) ∗
        "HsentI" ∷ ghost_var γ.(spsc_sent_name) half sent ∗
        "HrecvI" ∷ ghost_var γ.(spsc_recv_name) half recv ∗
        "%Hrel"  ∷ ⌜sent = recv ++ inflight s⌝ ∗
        (match s with
        (* element-wise P on currently in-flight *)
         | chan_rep.Buffered buff => [∗ list] v ∈ buff, P v
         | chan_rep.SndWait v | chan_rep.SndDone v => P v
         | chan_rep.Closed draining =>
             [∗ list] v ∈ draining, P v        
           (* Park the producer permission here so we can't send or close on closed channel
            *)                          
           ∗ spsc_producer γ sent  
           (* Receiver must give up permission and observe that the channel is drained before 
           getting R *)                            
           ∗ (R sent ∨ spsc_consumer γ sent)
         | _ => True
         end)
    )%I.

Lemma wp_spsc_send γ ch (P : V → iProp Σ) (R : list V → iProp Σ)
                   (sent : list V) (v : V) :
  {{{  is_pkg_init channel ∗ is_spsc γ ch P R ∗ spsc_producer γ sent ∗ P v }}}
    ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v
  {{{ RET #(); spsc_producer γ (sent ++ [v]) }}}.
Proof.
Admitted.

Lemma wp_spsc_receive γ ch (ns:spsc_names) (P : V → iProp Σ) (R : list V → iProp Σ)
                      (received : list V) :
  {{{  is_pkg_init channel ∗ is_spsc γ ch P R ∗ spsc_consumer γ received }}}
    ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #()
  {{{ (v:V) (ok:bool), RET (#v, #ok);
      (if ok then P v ∗ spsc_consumer γ (received ++ [v])
            else R received)%I }}}.  
Proof.
Admitted.

Lemma wp_spsc_close γ ch P R sent :
  {{{ is_pkg_init channel ∗ is_spsc γ ch P R ∗ spsc_producer γ sent ∗ R sent }}}
    ch @ (ptrT.id channel.Channel.id) @ "Close" #t #()
  {{{ RET #(); True }}}.
Proof.
Admitted.

End spsc.