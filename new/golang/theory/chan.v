From New.golang.defn Require Export chan.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Import exception list mem loop typing struct proofmode.
From Perennial Require Import base.

Module chanstate.
Record t (V : Type) :=
  mk {
    cap : w64;
    closed : bool;

    sent : list V;
    received : nat; (* ≃ (list unit) *)
  }.
Global Arguments mk {V}.
Global Arguments cap {V} (_).
Global Arguments closed {V} (_).
Global Arguments sent {V} (_).
Global Arguments received {V} (_).
Global Instance settable (V : Type) : Settable (t V) :=
  settable! (mk (V:=V)) < cap; closed; sent; received >.
End chanstate.

Section chan.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!IntoVal V}.

Definition is_chan (ch : chan.t) : iProp Σ.
Admitted.
Global Instance is_chan_pers ch : Persistent (is_chan ch).
Admitted.
Definition own_chan (ch: chan.t) (s : chanstate.t V) : iProp Σ.
Admitted.
End chan.

Arguments is_chan {_ _ _ _ _ _} (_) {_} ch.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!IntoVal V} `{!IntoValTyped V t}.

Implicit Types v : V.
Implicit Types (s : chanstate.t V).

Lemma own_chan_is_chan ch s :
  own_chan ch s -∗ is_chan V ch.
Proof.
Admitted.

Lemma is_chan_not_nil ch :
  is_chan V ch -∗ ⌜ ch ≠ chan.nil ⌝.
Proof.
Admitted.

Definition receive_atomic_update ch Φ : iProp Σ :=
  is_chan V ch ∗
  |={⊤,∅}=>
    ▷∃ s, own_chan ch s ∗
          if decide (s.(chanstate.closed) = true ∧ length s.(chanstate.sent) ≤ s.(chanstate.received)) then
            (* the channel is closed and empty, so return the zero value and false *)
            (own_chan ch s ={∅,⊤}=∗ (Φ (#(default_val V), #false)%V))
          else
            (* notify the sender that this thread is receiving *)
            (own_chan ch (set chanstate.received S s) ={∅,⊤}=∗
             (* receive the value from the sender *)
             (|={⊤,∅}=> ▷∃ (s' : chanstate.t V),
                           own_chan ch s' ∗
                           (∀ v, ⌜ s'.(chanstate.sent) !! s.(chanstate.received) = Some v ⌝ -∗
                                 own_chan ch s' ={∅,⊤}=∗ Φ (#v, #true)%V))).

Definition send_atomic_update ch (v : V) Φ : iProp Σ :=
  (* send the value *)
  is_chan V ch ∗
  |={⊤,∅}=>
    ▷∃ s, own_chan ch s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
          (own_chan ch (s <| chanstate.sent := s.(chanstate.sent) ++ [v] |>) ={∅,⊤}=∗
           (* get notified that there was enough space of the buffer for it *)
           (|={⊤,∅}=>
              ▷∃ (s' : chanstate.t V),
                  own_chan ch s' ∗
                  (⌜ length s.(chanstate.sent) < s'.(chanstate.received) + uint.nat (s.(chanstate.cap)) ⌝ -∗
                   own_chan ch s' ={∅,⊤}=∗ Φ #()))).

(* A (blocking) send/receive operation consists of an atomic update that
   "signals then observes." A non-blocking operation consists of an atomic
   update that "observes then signals." *)

Definition nonblocking_receive_atomic_update ch Φok Φnotready : iProp Σ :=
  is_chan V ch ∗
  |={⊤,∅}=>
    ▷∃ s, own_chan ch s ∗
          match s.(chanstate.sent) !! s.(chanstate.received) with
          | None =>
              (if s.(chanstate.closed) then
                 (own_chan ch s ={∅,⊤}=∗ (Φok (#(default_val V), #false)%V))
               else own_chan ch s ={∅,⊤}=∗ Φnotready)
          | Some v => own_chan ch (set chanstate.received S s) ={∅,⊤}=∗ Φok (#v, #true)%V
          end
.

Definition nonblocking_send_atomic_update ch (v : V) Φok Φnotready : iProp Σ :=
  is_chan V ch ∗
  |={⊤,∅}=>
    ▷∃ s, own_chan ch s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
          (if decide (length s.(chanstate.sent) < s.(chanstate.received) + uint.nat (s.(chanstate.cap))) then
              own_chan ch (s <| chanstate.sent := s.(chanstate.sent) ++ [v] |>) ={∅,⊤}=∗ Φok
            else
              own_chan ch s ={∅,⊤}=∗ Φnotready).

Lemma wp_chan_make cap :
  {{{ True }}}
    chan.make #t #cap
  {{{ (c : chan.t) (init : list V), RET #c; own_chan c (chanstate.mk cap false init (length init)) }}}.
Proof.
Admitted.

Lemma wp_chan_receive ch :
  ∀ Φ,
  ▷ receive_atomic_update ch Φ -∗
  WP chan.receive #ch {{ Φ }}.
Proof.
Admitted.

Lemma wp_chan_send ch (v : V) :
  ∀ Φ,
  ▷ send_atomic_update ch v Φ -∗
  WP chan.send #ch #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_chan_close ch :
  ∀ Φ,
  is_chan V ch -∗
  ▷ (|={⊤,∅}=> ▷ ∃ s, own_chan ch s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
                 (own_chan ch (s <|chanstate.closed := true |>) ={∅,⊤}=∗ Φ #())
  ) -∗
  WP chan.close #ch {{ Φ }}.
Proof.
Admitted.

Definition for_chan_postcondition_def P Φ bv : iProp Σ :=
            ⌜ bv = continue_val ⌝ ∗ P ∨
            (∃ (v : val), ⌜ bv = execute_val v ⌝ ∗ P) ∨
            ⌜ bv = break_val ⌝ ∗ Φ (execute_val #()) ∨
            (∃ (v : val), ⌜ bv = return_val v ⌝ ∗ Φ bv).
Program Definition for_chan_postcondition := sealed @for_chan_postcondition_def.
Definition for_chan_postcondition_unseal : for_chan_postcondition = _ := seal_eq _.

Lemma wp_for_chan_range P ch (body : func.t) :
  ∀ Φ,
  P -∗
  is_chan V ch -∗
  □(P -∗
    |={⊤,∅}=>
      ▷∃ s, own_chan ch s ∗
            if decide (s.(chanstate.closed) = true ∧ length s.(chanstate.sent) ≤ s.(chanstate.received)) then
              (* the channel is closed and empty, so the loop exits *)
              (own_chan ch s ={∅,⊤}=∗ (Φ (execute_val #())))
            else
              (* notify the sender that this thread is receiving *)
              (own_chan ch (set chanstate.received S s) ={∅,⊤}=∗
               (* receive the value from the sender *)
               (|={⊤,∅}=>
                  ▷∃ (s' : chanstate.t V),
                      own_chan ch s' ∗
                      (∀ v, ⌜ s'.(chanstate.sent) !! s.(chanstate.received) = Some v ⌝ -∗
                            own_chan ch s' ={∅,⊤}=∗ WP #body #v {{ for_chan_postcondition P Φ }})))
    ) -∗
  WP chan.for_range #ch #body {{ Φ }}.
Proof.
Admitted.

Lemma wp_for_chan_post_do (v : val) P Φ :
  P -∗
  for_chan_postcondition P Φ (execute_val v).
Proof.
  iIntros "H". rewrite for_chan_postcondition_unseal /for_chan_postcondition_def.
  eauto 10 with iFrame.
Qed.

Lemma wp_for_chan_post_continue P Φ :
  P -∗
  for_chan_postcondition P Φ continue_val.
Proof.
  iIntros "H". rewrite for_chan_postcondition_unseal /for_chan_postcondition_def.
  eauto 10 with iFrame.
Qed.

Lemma wp_for_chan_post_break P Φ :
  Φ (execute_val #()) -∗
  for_chan_postcondition P Φ break_val.
Proof.
  iIntros "H". rewrite for_chan_postcondition_unseal /for_chan_postcondition_def.
  eauto 10 with iFrame.
Qed.

Lemma wp_for_chan_post_return P Φ (v : val) :
  Φ (return_val v) -∗
  for_chan_postcondition P Φ (return_val v).
Proof.
  iIntros "H". rewrite for_chan_postcondition_unseal /for_chan_postcondition_def.
  eauto 10 with iFrame.
Qed.

End proof.

(** Tactic for convenient chan loop reasoning. First use [iAssert] to generalize the
    current context to the loop invariant, then apply this tactic. Use
    [wp_for_chan_post] for the leaves of the proof. *)
Ltac wp_for_chan_core :=
  wp_bind (chan.for_range _ _); (iApply (wp_for_chan_range (IntoValTyped0:=?[ivt]) with "[-]"));
  [ by iNamedAccu
  | (by iFrame "#" || fail "wp_for_chan_core: could not solve [is_chan] by [iFrame ""#""]. ")
  | iIntros "!# __CTX"; iNamed "__CTX" ]; instantiate(ivt:=ltac:(tc_solve)).

(** Automatically apply the right theorem for [for_chan_postcondition] *)
Ltac wp_for_chan_post_core :=
  lazymatch goal with
  | |- environments.envs_entails _ (for_chan_postcondition _ _ _) =>
      (* this could use pattern matching but it's not really necessary,
      unification will handle it *)
      first [
          iApply wp_for_chan_post_do
        | iApply wp_for_chan_post_continue
        | iApply wp_for_chan_post_break
        | iApply wp_for_chan_post_return
        ]
  | _ => fail "wp_for_chan_post: not a for_chan_postcondition goal"
  end.

Module chan.
Section op.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Inductive op :=
| select_send_f (v : val) (ch : chan.t) (handler : func.t)
| select_receive_f (ch : chan.t) (handler : func.t).

Global Instance into_val_op : IntoVal op :=
  {|
    to_val_def := λ o,
        match o with
        | select_send_f v ch f => InjLV (v, #ch, #f)
        | select_receive_f ch f => InjRV (#ch, #f)
        end
  |}.

Global Instance wp_select_send (v : val) ch f :
  PureWp True (chan.select_send v #ch #f)
    #(select_send_f v ch f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

Global Instance wp_select_receive ch f :
  PureWp True (chan.select_receive #ch #f)
    #(select_receive_f ch f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

Inductive default :=
| select_default_f  : func.t → default.

Global Instance into_val_default : IntoVal default :=
  {|
    to_val_def := λ s,
        match s with
        | select_default_f f => InjRV #f
        end
  |}.

Global Instance wp_select_default f:
  PureWp True (chan.select_default #f) #(select_default_f f).
Proof.
  pure_wp_start. repeat rewrite to_val_unseal /=. by iApply "HΦ".
Qed.

End op.
End chan.

Arguments receive_atomic_update {_ _ _ _ _ _} (_) {_ _ _} (_ _).
Arguments nonblocking_receive_atomic_update {_ _ _ _ _ _} (_) {_ _ _} (_ _ _).

Section select_proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

Lemma wp_chan_select_blocking (cases : list chan.op) :
  ∀ Φ,
  ([∧ list] case ∈ cases,
     match case with
     | chan.select_send_f send_val send_chan send_handler =>
         (∃ V (v : V) `(!IntoVal V),
             ⌜ send_val = #v ⌝ ∗
             send_atomic_update send_chan v (λ _, WP #send_handler #() {{ Φ }}))
     | chan.select_receive_f recv_chan recv_handler =>
         (∃ V t `(!IntoVal V) `(!IntoValTyped V t),
             receive_atomic_update V recv_chan (λ v, WP #recv_handler v {{ Φ }}))
     end
  ) -∗
  WP chan.select #cases chan.select_no_default {{ Φ }}.
Proof.
Admitted.

Lemma wp_chan_select_nonblocking (Φnrs : list (iProp Σ)) (cases : list chan.op) (def : func.t) :
  ∀ Φ,
  length Φnrs = length cases →
  (([∧ list] i ↦ case ∈ cases,
      let Φnotready := default False (Φnrs !! i) in
      match case with
      | chan.select_send_f send_val send_chan send_handler =>
          (∃ V (v : V) `(!IntoVal V),
              ⌜ send_val = #v ⌝ ∗
              nonblocking_send_atomic_update send_chan v (WP #send_handler #() {{ Φ }}) Φnotready)
      | chan.select_receive_f recv_chan recv_handler =>
          (∃ V t `(!IntoVal V) `(!IntoValTyped V t),
              nonblocking_receive_atomic_update V recv_chan (λ v, WP #recv_handler v {{ Φ }}) Φnotready)
      end) ∧
   ([∗] Φnrs -∗ WP #def #() {{ Φ }})
  ) -∗
  WP chan.select #cases #(chan.select_default_f def) {{ Φ }}.
Proof.
Admitted.

End select_proof.
