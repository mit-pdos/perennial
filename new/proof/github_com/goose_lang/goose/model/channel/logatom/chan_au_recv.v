From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
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

(* ================ BUFFERED CHANNEL ================ *)

(* Non-blocking buffered receive - success/failure split *)
Definition buffered_try_receive_atomic_update
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) (Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Open buffered channel case *)
      ∃ queue cap, own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer queue cap))) γ ∗
      (if decide (length queue > 0) then
         (* Success path: dequeue a value *)
         match queue with
         | [] => False (* impossible given length > 0 *)
         | v :: rest => 
           (own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer rest cap))) γ ={∅,⊤}=∗ Φsuccess v true)
         end
       else
         (* No items available: would block *)
         (own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer queue cap))) γ ={∅,⊤}=∗ Φfailure))
    ∨
    (* Closed channel case *)
    own_channel ch chan_state.Closed γ ∗
    (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)).

(* Blocking buffered receive - guaranteed eventual success *)
Definition buffered_receive_atomic_update 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Path 1: Get a value from buffer (eventually) *)
      ∃ queue cap v rest, 
      ⌜queue = v :: rest⌝ ∗
      own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer queue cap))) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Buffered (chan_state.Buffer rest cap))) γ ={∅,⊤}=∗ Φsuccess v true)
    ∨
     (* Path 2: Observe closed *)
     own_channel ch chan_state.Closed γ ∗
     (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)).

(* ================ UNBUFFERED CHANNEL ================ *)

(* Non-blocking unbuffered receive - can only accept existing sender offers *)
Definition unbuffered_try_nonblocking_receive_atomic_update
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) (Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Success: complete waiting sender's offer *)
      ∃ v, own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndWait v))) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.RcvDone))) γ ={∅,⊤}=∗ Φsuccess v true)
    ∨
     (* Failure: no sender waiting, or channel busy *)
     (∃ ub, own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ∗
      ⌜∀ v, ub ≠ chan_state.SndWait v⌝ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ={∅,⊤}=∗ Φfailure))
    ∨
     (* Channel is closed *)
     (own_channel ch chan_state.Closed γ ∗
     (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false))).

(* Blocking unbuffered receive - can make offers *)
Definition unbuffered_try_blocking_receive_atomic_update
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) (Φfailure: iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Path 1: Complete existing sender offer *)
      ∃ v, own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndWait v))) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.RcvDone))) γ ={∅,⊤}=∗ Φsuccess v true)
    ∨
     (* Path 2: Make receiver offer (two-phase) *)
     own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ∗
     (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.RcvWait)) γ ={∅,⊤}=∗ 
       (* Second phase: check if offer was accepted *)
       |={⊤,∅}=> ▷((* Offer accepted by sender *)
                   ∃ v, own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.RcvDone))) γ ∗
                   (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ={∅,⊤}=∗ Φsuccess v true)
                 ∨
                  (* Channel was closed *)
                  own_channel ch chan_state.Closed γ ∗
                  (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)
                 ∨
                  (* Offer rescinded *)
                  own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.RcvWait)) γ ∗
                  (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ={∅,⊤}=∗ Φfailure)))
    ∨
     (* Failure: channel busy with other exchange *)
     (∃ ub, own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ∗
      ⌜ub ≠ chan_state.Idle ∧ (∀ v, ub ≠ chan_state.SndWait v)⌝ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered ub)) γ ={∅,⊤}=∗ Φfailure))
    ∨
     (* Channel is closed *)
     own_channel ch chan_state.Closed γ ∗
     (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)).

(* Guaranteed eventual success for blocking receive *)
Definition unbuffered_receive_atomic_update 
  (ch: loc) (γ: chan_names) (Φsuccess: V → bool → iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=> 
    ▷((* Path 1: Immediate completion with waiting sender *)
      ∃ v, own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.SndWait v))) γ ∗
      (own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.RcvDone))) γ ={∅,⊤}=∗ 
        own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ∗ Φsuccess v true)
    ∨
     (* Path 2: Make offer and eventually get accepted *)
     own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ∗
     (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.RcvWait)) γ ={∅,⊤}=∗ 
       |={⊤,∅}=> ▷((∃ v, own_channel ch (chan_state.Open (chan_state.Unbuffered (chan_state.RcvDone))) γ ∗
                        (own_channel ch (chan_state.Open (chan_state.Unbuffered chan_state.Idle)) γ ={∅,⊤}=∗ Φsuccess v true))
                  ∨
                   (* Observe closed *)
                   own_channel ch chan_state.Closed γ ∗
                   (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)))
    ∨
     (* Path 3: Observe closed *)
     own_channel ch chan_state.Closed γ ∗
     (own_channel ch chan_state.Closed γ ={∅,⊤}=∗ Φsuccess (default_val V) false)).

(* ================ GENERIC CHANNEL SPECS (Pattern Matching) ================ *)

Definition chan_receive_atomic_update ch (γ: chan_names) (Φsuccess : V → bool → iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    match s with
    | chan_state.Open (chan_state.Buffered _) =>
        buffered_receive_atomic_update ch γ Φsuccess
    | chan_state.Open (chan_state.Unbuffered _) =>
        unbuffered_receive_atomic_update ch γ Φsuccess
    | chan_state.Closed => 
        own_channel ch s γ ={∅,⊤}=∗ Φsuccess (default_val V) false
    end.

Definition chan_nonblocking_receive_atomic_update ch (γ: chan_names) (Φsuccess : V → bool → iProp Σ) (Φnotready : iProp Σ) : iProp Σ :=
  is_channel ch γ ∗
  |={⊤,∅}=>
    ▷∃ s, own_channel ch s γ ∗
    match s with
    | chan_state.Open (chan_state.Buffered _) =>
        buffered_try_receive_atomic_update ch γ Φsuccess Φnotready
    | chan_state.Open (chan_state.Unbuffered _) =>
        unbuffered_try_nonblocking_receive_atomic_update ch γ Φsuccess Φnotready  
    | chan_state.Closed =>
        own_channel ch s γ ={∅,⊤}=∗ Φsuccess (default_val V) false
    end.

Lemma wp_Receive (ch: loc) (γ: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch γ -∗
  ▷(chan_receive_atomic_update ch γ (λ v ok, Φ (#v, #ok)%V)) -∗
  WP ch @ (ptrT.id channel.Channel.id) @ "Receive" #t #() {{ Φ }}.
Proof.
Admitted.

End atomic_specs.
