From New.golang.defn Require Export chan.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Export exception list mem loop typing struct proofmode.

Module chan.
  Definition t := loc.
End chan.

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
(* FIXME: should this take an explicit V? *)
Axiom is_chan : ∀ (c : chan.t), iProp Σ.
Axiom is_chan_pers : ∀ c, Persistent (is_chan c).
Global Existing Instance is_chan_pers.
Axiom own_chan : ∀ `{!IntoVal V} (c : chan.t) (s : chanstate.t V), iProp Σ.
End chan.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!IntoVal V, !IntoValTyped V t}.

Implicit Types v : V.
Implicit Types (s : chanstate.t V).

Lemma wp_chan_make cap :
  {{{ True }}}
    chan.make t #cap
  {{{ (c : chan.t) (init : list V), RET #c; own_chan c (chanstate.mk cap false init (length init)) }}}.
Proof.
Admitted.

Definition receive_atomic_update ch Φ : iProp Σ :=
  |={⊤,∅}=>
    ▷∃ s, own_chan ch s ∗
          if decide (s.(chanstate.closed) = true ∧ s.(chanstate.received) = length s.(chanstate.sent)) then
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

Lemma wp_chan_receive ch :
  ∀ Φ,
  is_chan ch -∗
  ▷ receive_atomic_update ch Φ -∗
  WP chan.receive #ch {{ Φ }}.
Proof.
Admitted.

Definition send_atomic_update ch (v : V) Φ : iProp Σ :=
  (* send the value *)
  |={⊤,∅}=>
    ▷∃ s, own_chan ch s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
          (own_chan ch (s <| chanstate.sent := s.(chanstate.sent) ++ [v] |>) ={∅,⊤}=∗
           (* get notified that there was enough space of the buffer for it *)
           (|={⊤,∅}=>
              ▷∃ (s' : chanstate.t V),
                  own_chan ch s' ∗
                  (⌜ length s.(chanstate.sent) < s'.(chanstate.received) + uint.nat (s.(chanstate.cap)) ⌝ -∗
                   own_chan ch s' ={∅,⊤}=∗ Φ #()))).

Lemma wp_chan_send ch (v : V) :
  ∀ Φ,
  is_chan ch -∗
  ▷ send_atomic_update ch v Φ -∗
  WP chan.send #ch #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_chan_close ch :
  ∀ Φ,
  is_chan ch -∗
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
Program Definition for_chan_postcondition := unseal (_:seal (@for_chan_postcondition_def)). Obligation 1. by eexists. Qed.
Definition for_chan_postcondition_unseal : for_chan_postcondition = _ := seal_eq _.

Lemma wp_for_chan_range P ch (body : func.t) :
  ∀ Φ,
  P -∗
  is_chan ch -∗
  □(P -∗
    |={⊤,∅}=>
      ▷∃ s, own_chan ch s ∗
            if decide (s.(chanstate.closed) = true ∧ s.(chanstate.received) = length s.(chanstate.sent)) then
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
  wp_bind (chan.for_range _ _); iApply (wp_for_chan_range with "[-]");
  [ by iNamedAccu
  |
  | iIntros "!# __CTX"; iNamed "__CTX" ].

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

Section select_proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.

(* TODO: require [is_chan] for everything. *)
(* TODO: combine the chans+(vals)+handlers into one list? *)
Lemma wp_chan_select_blocking (send_chans recv_chans : list chan.t)
  (send_vals : list val) (send_handlers recv_handlers : list func.t) :
  ∀ Φ,
  ((∀ idx send_chan send_val send_handler,
      ⌜ send_chans !! idx = Some send_chan ∧ send_vals !! idx = Some send_val ∧
      send_handlers !! idx = Some send_handler ⌝ →
      ∃ V (v : V) `(!IntoVal V),
        ⌜ send_val = #v ⌝ ∗
        send_atomic_update send_chan v (λ _, WP #send_handler #() {{ Φ }})
   ) ∧
   (∀ idx recv_chan recv_handler,
      ⌜ recv_chans !! idx = Some recv_chan ∧ recv_handlers !! idx = Some recv_handler ⌝ →
      ∃ V t `(!IntoVal V) `(!IntoValTyped V t),
        receive_atomic_update (V:=V) recv_chan (λ v, WP #recv_handler v {{ Φ }})
  )) -∗
  WP chan.select (* #send_vals *) #send_chans #recv_chans (InjLV #()) {{ Φ }}.
Proof.
Admitted.

End select_proof.

Section onetime_barrier.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!ghost_varG Σ ()}.

Implicit Types (s : chanstate.t unit).

Record params :=
  {
    gauge_init : nat; (* XXX: putting "gauge" in the name because this would
                       change under a `chan` gauge transformation. *)
    send_gn : gname;
    recv_gn : gname;
  }.
Implicit Types γ : params.

Definition own_send_tok γ := ghost_var γ.(send_gn) 1 ().
Definition own_recv_tok γ := ghost_var γ.(recv_gn) 1 ().

Definition is_onetime_barrier γ (ch : chan.t) Sd Rv : iProp Σ :=
  is_chan ch ∗
  inv nroot (
      ∃ s,
        "Hch" ∷ own_chan ch s ∗
        "%Hcap" ∷ ⌜ s.(chanstate.cap) = W64 0 ⌝ ∗
        "%Hopen" ∷ ⌜ s.(chanstate.closed) = false ⌝ ∗
        "%Hoffset_r" ∷ ⌜ γ.(gauge_init) ≤ s.(chanstate.received) ⌝%nat ∗
        "%Hoffset_s" ∷ ⌜ γ.(gauge_init) ≤ length s.(chanstate.sent) ⌝%nat ∗
        "Hr" ∷ match (s.(chanstate.received) - γ.(gauge_init))%nat with
          | O => True
          | S _ => (Rv ∨ own_send_tok γ)
          end ∗
        "Hs" ∷ match (length s.(chanstate.sent) - γ.(gauge_init))%nat with
          | O => True
          | S _ => (Sd ∨ own_recv_tok γ)
          end
    ).

Lemma start_onetime_barrier Sd Rv ch s:
  s.(chanstate.cap) = (W64 0) →
  s.(chanstate.closed) = false →
  s.(chanstate.received) = length s.(chanstate.sent) →
  is_chan ch -∗
  own_chan ch s ={⊤}=∗
  ∃ γ, is_onetime_barrier γ ch Sd Rv ∗
       own_recv_tok γ ∗
       own_send_tok γ.
Proof.
  intros.
  iIntros "#? Hchan".
  iMod (ghost_var_alloc ()) as "[% ?]".
  iMod (ghost_var_alloc ()) as "[% ?]".
  iExists _.
  instantiate (1:=(ltac:(econstructor))). simpl.
  iFrame "#". iFrame. simpl.
  iApply inv_alloc.
  iNext. iFrame "∗%".
  instantiate (1:=s.(chanstate.received)).
  iSplitR; first word.
  iSplitR; first word.
  rewrite H1 Nat.sub_diag //.
Qed.

Lemma wp_onetime_barrier_receive γ ch Sd Rv :
  {{{
      is_onetime_barrier γ ch Sd Rv ∗
      own_recv_tok γ ∗
      Rv
  }}}
    chan.receive #ch
  {{{
      RET (#(), #true); Sd
  }}}.
Proof.
  iIntros (?) "((#Hchan & #Hinv) & Htok & HR) HΦ".
  wp_apply (wp_chan_receive (V:=()) with "[$]").

  (* send Rv *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame.
  rewrite Hopen.
  iIntros "Hch".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-Htok HΦ]").
  { iNext. iFrame "∗%".
    simpl. iSplitR; first word.
    rewrite Nat.sub_succ_l //. iFrame.
  }
  iModIntro.

  (* get Sd *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame.
  iIntros "* % Hch".

  edestruct (length _ - _)%nat eqn:?.
  { simpl in *. exfalso. apply lookup_lt_Some in H. lia. }
  iDestruct "Hs" as "[Hs|Hbad]".
  2:{ iCombine "Hbad Htok" gives %[Hbad _]. done. }
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-HΦ Hs]").
  { iNext. iFrame "∗%". destruct (_ - _)%nat; iFrame. }
  iModIntro.
  destruct v.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_onetime_barrier_send γ ch Sd Rv :
  {{{
      is_onetime_barrier γ ch Sd Rv ∗
      own_send_tok γ ∗
      Sd
  }}}
    chan.send #ch #()
  {{{
      RET #(); Rv
  }}}.
Proof.
  iIntros (?) "((#Hchan & #Hinv) & Htok & HR) HΦ".
  wp_apply (wp_chan_send (V:=()) with "[$]").

  (* send Sd *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame "∗%".
  iIntros "Hch".
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-Htok HΦ]").
  { iNext. iFrame "∗%". iSplitR.
    { rewrite length_app /=. iPureIntro. lia. }
    iClear "Hs". by destruct Nat.sub; iFrame.
  }
  iModIntro.

  (* get Rv *)
  iInv "Hinv" as "Hi" "Hclose".
  iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
  iNext. iNamed "Hi".
  iExists _; iFrame.
  iIntros "* % Hch".

  edestruct (chanstate.received s0 - _)%nat eqn:?.
  { simpl in *. exfalso. word. }
  iDestruct "Hr" as "[Hr|Hbad]".
  2:{ iCombine "Hbad Htok" gives %[Hbad _]. done. }
  iMod "Hmask" as "_".
  iMod ("Hclose" with "[-HΦ Hr]").
  { iNext. iFrame "∗%". by destruct Nat.sub; iFrame. }
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End onetime_barrier.
