From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop invariants ghost_var.
From RecordUpdate Require Import RecordSet.
From Perennial Require Import NamedProps.
Import RecordSetNotations.

Module chanstate.
Record t (V : Type) :=
  mk {
    closed : bool;
    sent : list V;
    received : nat; (* ≃ (list unit) *)
  }.
Global Arguments mk {V}.
Global Arguments closed {V} (_).
Global Arguments sent {V} (_).
Global Arguments received {V} (_).
Global Instance settable (V : Type) : Settable (t V) :=
  settable! (mk (V:=V)) < closed; sent; received >.
End chanstate.

Module unbuf_chan_from_exchange.
Section proof.
Context `{!invGS Σ}.
Context (V : Type).
Record chan_params :=
  mk_chan_params
    {
      Sd : V → iProp Σ;
      Rv : iProp Σ
    }.

Axiom own_close : iProp Σ.
Axiom is_closed : iProp Σ.
Axiom default_v : V.

Definition N := nroot.@"chan".

Definition chan_send_spec ρ v Φ : iProp Σ :=
  £ 3 -∗ |={⊤,∅}=> (own_close ∗ ρ.(Sd) v ∗ (own_close ={∅,⊤}=∗ ρ.(Rv) ={⊤}=∗ Φ)).

Definition chan_receive_spec ρ Φ : iProp Σ :=
  £ 3 -∗ |={⊤}=> (ρ.(Rv) ∗
            (∀ v, ρ.(Sd) v ={⊤}=∗ Φ (v, true)) ∧
            (is_closed ={⊤}=∗ Φ (default_v, false))).

Definition goal_send_spec own_chan (v : V) Φ : iProp Σ :=
  (* send the value *)
  |={⊤,↑N}=>
    ▷∃ s, own_chan s ∗ ⌜ s.(chanstate.closed) = false ⌝ ∗
          (own_chan (s <| chanstate.sent := s.(chanstate.sent) ++ [v] |>) ={↑N,⊤}=∗
           (* get notified that there was enough space of the buffer for it *)
           (|={⊤,↑N}=>
              ▷∃ (s' : chanstate.t V),
                  own_chan s' ∗
                  (⌜ length s.(chanstate.sent) ≤ s'.(chanstate.received)  ⌝ -∗
                   own_chan s' ={↑N,⊤}=∗ Φ))).

Definition goal_receive_spec own_chan Φ : iProp Σ :=
  |={⊤,↑N}=>
    ▷∃ s, own_chan s ∗
          if decide (s.(chanstate.closed) = true ∧ length s.(chanstate.sent) ≤ s.(chanstate.received)) then
            (* the channel is closed and empty, so return the zero value and false *)
            (own_chan s ={↑N,⊤}=∗ (Φ (default_v, false)))
          else
            (* notify the sender that this thread is receiving *)
            (own_chan (set chanstate.received S s) ={↑N,⊤}=∗
             (* receive the value from the sender *)
             (|={⊤,↑N}=> ▷∃ (s' : chanstate.t V),
                           own_chan s' ∗
                           (∀ v, ⌜ s'.(chanstate.sent) !! s.(chanstate.received) = Some v ⌝ -∗
                                 own_chan s' ={↑N,⊤}=∗ Φ (v, true)))).

Context `{!ghost_varG Σ (chanstate.t V)}.
Lemma fact :
  ⊢ own_close ={⊤}=∗
    ∃ ρ own_chan,
        own_chan (chanstate.mk false [] 0) ∗
        □ (∀ v Φ, goal_send_spec own_chan v Φ -∗ chan_send_spec ρ v Φ) ∗
        □ (∀ Φ, goal_receive_spec own_chan Φ -∗ chan_receive_spec ρ Φ).
Proof.
  iIntros "Hcc".
  iMod (ghost_var_alloc (chanstate.mk false [] 0)) as (γ) "[H Hc]".
  set (own_chan (s : chanstate.t V) := ghost_var γ (1/2) s).
  iMod (inv_alloc (nroot.@"chan") _ (
            ∃ st,
              "Hc" ∷ own_chan st ∗
              "Hclosed" ∷ (match st.(chanstate.closed) with
                           | false => own_close
                           | true => is_closed
                           end) ∗
              "Hsent" ∷ (True)
          )%I with "[H Hcc]") as "#Hinv".
  { iFrame. simpl. iFrame. }
  iModIntro.
  iExists (mk_chan_params ?[Sd] ?[Rv]).
  iExists own_chan. iFrame "Hc".
  iSplit.
  - (* send *)
    iIntros "!# * Hau (Hlc & Hlc2 & Hlc3)".
    iMod "Hau". iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iMod (lc_fupd_elim_later with "[$] Hau") as "Hau".
    iApply fupd_mask_intro. { solve_ndisj. } iIntros "Hmask".
    iDestruct "Hau" as "(% & Hc2 & %Hclose & Hau)".
    iNamed "Hi".
    iCombine "Hc Hc2" gives %[_ ->]. rewrite Hclose.
    iFrame "Hclosed". simpl.
    iSplitR. { admit. }
    iIntros "Hclosed".
    iMod (ghost_var_update_2 with "Hc Hc2") as "[Hc Hc2]".
    { rewrite Qp.half_half //. }
    iMod "Hmask" as "_".
    iSpecialize ("Hau" with "[$]").
    iMod ("Hclose" with "[-Hau Hlc]") as "_".
    { iNext. iFrame.  simpl. rewrite Hclose. iFrame. }
    iMod "Hau". iModIntro.
    iIntros "HRv".
    iMod "Hau".
    iMod (lc_fupd_elim_later with "[$] Hau") as "(%s' & Hc & Hau)".
    admit.
  - (* receive *)
    iIntros "!# * Hau (Hlc & Hlc2 & Hlc3)".
    iMod "Hau". iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iMod (lc_fupd_elim_later with "[$] Hau") as "Hau".
    iDestruct "Hau" as "(% & Hc2 & Hau)". iNamed "Hi".
    iCombine "Hc Hc2" gives %[_ ->].
    destruct_decide (decide (chanstate.closed s = true)) as Hclose.
    + rewrite Hclose. admit.
    + apply not_true_is_false in Hclose. rewrite Hclose /=.
      iMod (ghost_var_update_2 with "Hc Hc2") as "[Hc Hc2]".
      { rewrite Qp.half_half //. }
      iSpecialize ("Hau" with "[$]").
      iMod ("Hclose" with "[-Hau Hlc]") as "_".
      { iNext. iFrame.  simpl. rewrite Hclose. iFrame. }
      iMod "Hau". iModIntro.
      iSplitR. { admit. }
      iSplit.
      2:{ admit. }
      iIntros "%v HSd".
Abort.
End proof.
End unbuf_chan_from_exchange.


