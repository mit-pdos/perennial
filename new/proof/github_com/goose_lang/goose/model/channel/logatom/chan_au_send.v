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


(* ================ BUFFERED CHANNEL SPECS ================ *)

(* Non-blocking buffered send - success/failure split *)
Definition buffered_try_send_atomic_update 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷∃ queue cap, own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer queue cap))) γ ∗
    (* Branch on available capacity *)
    (if decide (length queue < cap) then
       (* Success path: enqueue the value *)
       (own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer (queue ++ [v]) cap))) γ ={∅,⊤}=∗ Φsuccess)
     else
       (* Failure path: buffer is full *)
       (own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer queue cap))) γ ={∅,⊤}=∗ Φfailure)).

(* Blocking buffered send - guaranteed eventual success *)
Definition buffered_send_atomic_update 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷∃ queue cap, own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer queue cap))) γ ∗
    (* Will eventually succeed when capacity becomes available *)
    (own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer (queue ++ [v]) cap))) γ ={∅,⊤}=∗ Φsuccess).

(* ================ UNBUFFERED CHANNEL SPECS ================ *)

(* Non-blocking unbuffered send - can only accept existing receiver offers *)
Definition unbuffered_try_nonblocking_send_atomic_update 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Success: complete waiting receiver's offer *)
      own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.RcvWait)) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndDone v))) γ ={∅,⊤}=∗ Φsuccess)
    ∨
     (* Failure: no receiver waiting, or channel busy *)
     (∃ ub, own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ∗
      ⌜ub ≠ chan_state.RcvWait⌝ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ={∅,⊤}=∗ Φfailure))
    ∨
     (* Channel is closed *)
     (own_channel ch chan_state.Closed γ ∗
     False) (* Send on closed channel - should panic *)).

(* Blocking unbuffered send - can make offers *)  
Definition unbuffered_try_blocking_send_atomic_update 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Path 1: Complete existing receiver offer *)
      own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.RcvWait)) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndDone v))) γ ={∅,⊤}=∗ Φsuccess)
    ∨
     (* Path 2: Make sender offer (two-phase) *)
     own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ∗
     (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndWait v))) γ ={∅,⊤}=∗ 
       (* Second phase: check if offer was accepted *)
       |={⊤,∅}=> ▷((* Offer accepted *)
                   own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndDone v))) γ ∗
                   (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ={∅,⊤}=∗ Φsuccess)
                 ∨
                  (* Offer rescinded *)
                  own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndWait v))) γ ∗
                  (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ={∅,⊤}=∗ Φfailure)))
    ∨
     (* Failure: channel busy with other exchange *)
     (∃ ub, own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ∗
      ⌜ub ≠ chan_state.Idle ∧ ub ≠ chan_state.RcvWait⌝ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ={∅,⊤}=∗ Φfailure))
    ∨
     (* Channel is closed *)
     (own_channel ch chan_state.Closed γ ∗
     False) (* Send on closed channel - should panic *)).

(* Guaranteed eventual success for blocking send *)
Definition unbuffered_send_atomic_update 
  (ch: loc) (v: V) (γ: chan_names) (Φsuccess: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Path 1: Immediate completion with waiting receiver *)
      own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.RcvWait)) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndDone v))) γ ={∅,⊤}=∗ 
        own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ∗ Φsuccess)
    ∨
     (* Path 2: Make offer and eventually get accepted *)
     own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ∗
     (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndWait v))) γ ={∅,⊤}=∗ 
       |={⊤,∅}=> ▷(own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndDone v))) γ ∗
                   (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ={∅,⊤}=∗ Φsuccess)))).

(* ================ GENERIC CHANNEL SPECS (Pattern Matching) ================ *)

Definition chan_send_atomic_update ch (v : V) (γ: chan_names) (Φsuccess : iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    match s with
    | chan_state.Open (chan_state.Buffered _) =>
        (* Delegate to proven buffered spec *)
        buffered_send_atomic_update ch v γ Φsuccess
    | chan_state.Open (chan_state.Unbuffered _) =>
        (* Delegate to proven unbuffered spec *)
        unbuffered_send_atomic_update ch v γ Φsuccess
    | chan_state.Closed => False
    end.

Definition chan_nonblocking_send_atomic_update ch (v : V) (γ: chan_names) (Φsuccess Φnotready : iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    match s with
    | chan_state.Open (chan_state.Buffered _) =>
        buffered_try_send_atomic_update ch v γ Φsuccess Φnotready
    | chan_state.Open (chan_state.Unbuffered _) =>
        unbuffered_try_nonblocking_send_atomic_update ch v γ Φsuccess Φnotready
    | chan_state.Closed => False
    end.

Lemma wp_Send 
  (ch: loc) (v: V) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch γ -∗
  ▷(chan_send_atomic_update ch v γ (Φ #())) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Send" #t #v  {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
