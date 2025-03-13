From New.golang.defn Require Export chan.
From iris.base_logic Require Export lib.ghost_var.
From New.golang.theory Require Export list mem loop typing struct proofmode.

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
  {{{ (c : chan.t), RET #c; own_chan c (chanstate.mk cap false ([] : list V) O) }}}.
Proof.
Admitted.

Lemma wp_chan_receive ch :
  ∀ Φ,
  is_chan ch -∗
  ▷(|={⊤,∅}=>
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
                                   own_chan ch s' ={∅,⊤}=∗ Φ (#v, #true)%V)))
  ) -∗
  WP chan.receive #ch {{ Φ }}.
Proof.
Admitted.

Lemma wp_chan_send ch (v : V) :
  ∀ Φ,
  is_chan ch -∗
  ▷((* send the value *)
    |={⊤,∅}=>
      ▷∃ s, own_chan ch s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
           (own_chan ch (s <| chanstate.sent := s.(chanstate.sent) ++ [v] |>) ={∅,⊤}=∗
            (* get notified that there was enough space of the buffer for it *)
            (|={⊤,∅}=> ▷∃ (s' : chanstate.t V),
               own_chan ch s' ∗
               (⌜ length s.(chanstate.sent) < s'.(chanstate.received) + uint.nat (s.(chanstate.cap)) ⌝ -∗
                own_chan ch s' ={∅,⊤}=∗ Φ #())))
  ) -∗
  WP chan.send #ch #v {{ Φ }}.
Proof.
Admitted.

Lemma wp_chan_close ch :
  ∀ Φ,
  is_chan ch -∗
  (|={⊤,∅}=> ∃ s, own_chan ch s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
                 (own_chan ch (s <|chanstate.closed := true |>) ={∅,⊤}=∗ Φ #())
  ) -∗
  WP chan.close #ch {{ Φ }}.
Proof.
Admitted.

Section onetime_barrier.
  Context `{!ghost_varG Σ ()}.
  Definition is_onetime_barrier γsend γrecv (ch : chan.t) Sd Rv : iProp Σ :=
    is_chan ch ∗
    inv nroot (
        ∃ s, own_chan ch s ∗
             ⌜ s.(chanstate.cap) = W64 0 ⌝ ∗
             ⌜ s.(chanstate.closed) = false ⌝ ∗
             match s.(chanstate.received) with
             | O => True
             | S _ => (Rv ∨ ghost_var γsend 1 ())
             end ∗
             match s.(chanstate.sent) with
             | [] => True
             | _::_ => (Sd ∨ ghost_var γrecv 1 ())
             end
      ).

  Lemma wp_onetime_barrier_receive γsend γrecv ch Sd Rv :
    {{{
        is_onetime_barrier γsend γrecv ch Sd Rv ∗
        ghost_var γrecv 1 () ∗
        Rv
    }}}
      chan.receive #ch
    {{{
        v, RET (#v, #true); Sd
    }}}.
  Proof.
    iIntros (?) "((#Hchan & #Hinv) & Htok & HR) HΦ".
    wp_apply (wp_chan_receive with "[$]").

    (* send Rv *)
    iInv "Hinv" as "Hi" "Hclose".
    iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
    iNext.
    iDestruct "Hi" as (?) "(? & % & %Hopen & Hs & Hr)".
    iExists _; iFrame.
    rewrite Hopen.
    iIntros "Hch".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[-Htok HΦ]").
    { iNext. iFrame. destruct (chanstate.received s); iFrame "∗%". }
    iModIntro.

    (* get Sd *)
    iInv "Hinv" as "Hi" "Hclose".
    iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
    iNext.
    iDestruct "Hi" as (?) "(? & % & % & Hs & Hr)".
    iExists _; iFrame.
    iIntros "* % Hch".

    destruct chanstate.sent.
    { simpl in *. done. }
    iDestruct "Hr" as "[Hr|Hbad]".
    2:{ iCombine "Hbad Htok" gives %[Hbad _]. done. }
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[-HΦ Hr]").
    { iNext. iFrame "∗%". destruct (chanstate.sent s0); iFrame "∗%". }
    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_onetime_barrier_send γsend γrecv ch Sd Rv v :
    {{{
        is_onetime_barrier γsend γrecv ch Sd Rv ∗
        ghost_var γsend 1 () ∗
        Sd
    }}}
      chan.send #ch #v
    {{{
        RET #(); Rv
    }}}.
  Proof.
    iIntros (?) "((#Hchan & #Hinv) & Htok & HR) HΦ".
    wp_apply (wp_chan_send with "[$]").

    (* send Sd *)
    iInv "Hinv" as "Hi" "Hclose".
    iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
    iNext.
    iDestruct "Hi" as (?) "(? & % & % & Hs & Hr)".
    iExists _; iFrame "∗%".
    iIntros "Hch".
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[-Htok HΦ]").
    { iNext. iFrame "∗%". destruct (chanstate.sent s); iFrame "∗%". }
    iModIntro.

    (* get Rv *)
    iInv "Hinv" as "Hi" "Hclose".
    iApply fupd_mask_intro; [set_solver | iIntros "Hmask"].
    iNext.
    iDestruct "Hi" as (?) "(? & % & % & Hs & Hr)".
    iExists _; iFrame.
    iIntros "* % Hch".

    destruct chanstate.received.
    { simpl in *. word. }
    iDestruct "Hs" as "[Hs|Hbad]".
    2:{ iCombine "Hbad Htok" gives %[Hbad _]. done. }
    iMod "Hmask" as "_".
    iMod ("Hclose" with "[-HΦ Hs]").
    { iNext. iFrame "∗%". destruct (chanstate.received s0); iFrame "∗%". }
    iModIntro.
    iApply "HΦ".
    iFrame.
  Qed.

End onetime_barrier.

End proof.
