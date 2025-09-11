From iris.proofmode Require Import proofmode.
From RecordUpdate Require Import RecordSet.
From Perennial Require Import NamedProps.
From New.experiments Require Import glob.
From iris.base_logic.lib Require Import iprop invariants ghost_var ghost_map token mono_nat.
From Perennial.base_logic.lib Require Import mono_list.
Import RecordSetNotations.

Module chanstate.
Record t (V : Type) :=
  mk {
    sent : list V;
    received : nat; (* ≃ (list unit) *)
  }.
Global Arguments mk {V}.
Global Arguments sent {V} (_).
Global Arguments received {V} (_).
Global Instance settable (V : Type) : Settable (t V) :=
  settable! (mk (V:=V)) < sent; received >.
End chanstate.

Module unbuf_chan_from_exchange.
Section proof.

Context `{!invGS Σ}.
Context (V : Type).
Record chan_params :=
  mk_chan_params
    {
      Sd : V → iProp Σ;
      Rv : iProp Σ;
      own_sender : iProp Σ;
      own_receiver : iProp Σ;
    }.

Axiom default_v : V.

Definition N := nroot.@"chan".

Definition chan_send_spec ρ v Φ : iProp Σ :=
  own_sender ρ ={⊤}=∗ Sd ρ v ∗ (ρ.(Rv) ={⊤}=∗ own_sender ρ ∗ Φ).

Definition chan_receive_spec ρ Φ : iProp Σ :=
  own_receiver ρ ={⊤}=∗ Rv ρ ∗ ∀ v, Sd ρ v ={⊤}=∗ own_receiver ρ ∗ Φ v.

Definition goal_send_spec own_chan (v : V) Φ : iProp Σ :=
  (* send the value *)
  |={⊤,↑N}=>
    ∃ s, own_chan s ∗
           (own_chan (s <| chanstate.sent := s.(chanstate.sent) ++ [v] |>) ={↑N,⊤}=∗
            (* get notified that there was enough space of the buffer for it *)
            (|={⊤,↑N}=>
               ∃ (s' : chanstate.t V),
               own_chan s' ∗
               (⌜ length s.(chanstate.sent) ≤ s'.(chanstate.received)  ⌝ -∗
                own_chan s' ={↑N,⊤}=∗ Φ))).

Definition goal_receive_spec own_chan Φ : iProp Σ :=
  |={⊤,↑N}=>
    ∃ s, own_chan s ∗
         (* notify the sender that this thread is receiving *)
         (own_chan (set chanstate.received S s) ={↑N,⊤}=∗
          (* receive the value from the sender *)
          (|={⊤,↑N}=> ▷∃ (s' : chanstate.t V),
                         own_chan s' ∗
                         (∀ v, ⌜ s'.(chanstate.sent) !! s.(chanstate.received) = Some v ⌝ -∗
                               own_chan s' ={↑N,⊤}=∗ Φ v))).

Context `{!ghost_varG Σ (chanstate.t V)}.
Context `{!ghost_varG Σ nat}.
Context `{!tokenG Σ}.
Context `{!ghost_mapG Σ string string}.
Context `{!mono_listG V Σ}.
Context `{!mono_natG Σ}.

Notation "5" := (pos_to_Qp 5) : Qp_scope.
Lemma split_to_fifths :
  (1 = 1/5 + 2/5 + 2/5)%Qp.
Proof. compute_done. Qed.

Lemma fact :
  ⊢ |={⊤}=>
        ∃ ρ own_chan,
  own_sender ρ ∗
  own_receiver ρ ∗
  own_chan (chanstate.mk [] 0) ∗
  □ (∀ v Φ, goal_send_spec own_chan v Φ -∗ chan_send_spec ρ v Φ) ∗
  □ (∀ Φ, goal_receive_spec own_chan Φ -∗ chan_receive_spec ρ Φ).
Proof.
  iMod (ghost_var_alloc (chanstate.mk [] 0)) as (γ) "[H Hc]".
  iMod (token_alloc) as (γsend) "Hsend".
  iMod (token_alloc) as (γreceive) "Hreceive".
  iMod (token_alloc) as (γcosend) "Hcosend".
  iMod (token_alloc) as (γcoreceive) "Hcoreceive".
  iMod (ghost_var_alloc 0) as (γcom) "Hcom".
  iMod (mono_list_own_alloc []) as (γsent) "[Hsent● _]".
  iMod (mono_nat_own_alloc 0) as (γreceived) "[Hreceived● _]".
  set (own_sender := token γsend).
  set (own_receiver := token γreceive).
  set (own_chan (s : chanstate.t V) := ghost_var γ (1/2) s).
  set (Sd (v : V) := (∃ committed,
                         ghost_var γcom (1/5)%Qp committed ∗
                         mono_list_idx_own γsent committed v
                     )%I).
  set (Rv := (∃ committed,
                 ghost_var γcom (1/5)%Qp committed ∗
                 mono_nat_lb_own γreceived committed
             )%I).

  iMod (inv_alloc (nroot.@"chan") _ (
            ∃ st,
              let committed := (min st.(chanstate.received) (length st.(chanstate.sent))) in
              "Hoc" ∷ own_chan st ∗
              "Hcom" ∷ ghost_var γcom (1/5) committed ∗

              "Hsent" ∷ mono_list_auth_own γsent 1 st.(chanstate.sent) ∗
              "Hrecevied" ∷ mono_nat_auth_own γreceived 1 st.(chanstate.received) ∗

              "Hsend" ∷ (
                  ("Hno_sender" ∷ token γcosend ∗
                   "Hcom_sender" ∷ ghost_var γcom (2/5) committed ∗
                    "%Hsent_eq_com" ∷ ⌜ length st.(chanstate.sent) = committed ⌝) ∨
                  ("Hsender" ∷ own_sender ∗
                   "%Hsent_eq_com_S" ∷ ⌜ length st.(chanstate.sent) = S committed ⌝)
                ) ∗

              "Hreceive" ∷ (
                  ("Hno_receiveer" ∷ token γcoreceive ∗
                   "Hcom_receiveer" ∷ ghost_var γcom (2/5) committed ∗
                    "%Hreceived_eq_com" ∷ ⌜ st.(chanstate.received) = committed ⌝) ∨
                  ("Hreceiveer" ∷ own_receiver ∗
                   "%Hreceived_eq_com_S" ∷ ⌜ st.(chanstate.received) = S committed ⌝)
                )
          )%I with "[-H Hsend Hreceive]") as "#Hinv".
  { iFrame.
    iEval (rewrite split_to_fifths) in "Hcom".
    iDestruct "Hcom" as "[[? Hs] Hr]". iFrame.
    iSplitL "Hcosend Hs".
    { iLeft. iFrame. simpl. done. }
    { iLeft. iFrame. simpl. done. }
  }
  iModIntro.
  iExists (mk_chan_params Sd Rv own_sender own_receiver).
  iExists own_chan. simpl. iFrame.
  iSplit.
  - (* send *)
    iIntros "!# * Hau Hsender".
    simpl.
    iMod "Hau". iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[] Hi") as "Hi".
    { admit. } (* lc *)
    iMod (lc_fupd_elim_later with "[] Hau") as "Hau".
    { admit. } (* lc *)
    iNamedSuffix "Hi" "_inv".
    iDestruct "Hsend_inv" as "[HH | Hbad]".
    2:{
      iNamedSuffix "Hbad" "_bad".
      iCombine "Hsender Hsender_bad" gives %[].
    }
    iNamed "HH".
    iRename "Hsender" into "Hsender_inv".
    iMod (mono_list_auth_own_update (st.(chanstate.sent) ++ [v]) with "Hsent_inv") as "[Hsent_inv #Hsent_lb]".
    { apply prefix_app_r. done. }
    iDestruct "Hau" as "(% & Hoc & Hau)".
    iCombine "Hoc_inv Hoc" gives %[_ ->].
    iMod (ghost_var_update_2 with "Hoc Hoc_inv") as "[Hoc Hoc_inv]".
    { rewrite Qp.half_half //. }
    iSpecialize ("Hau" with "[$Hoc]").
    iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]").
    {
      iNamed "Hi". (* iFrame "Hoc_inv" "Hsent_inv". iNext. iRight. iFrame.
    }
    iDestruct "Hcom_sender" as "[Hcom_sender Hcom_sender2]".
    *)
Admitted.


End proof.
End unbuf_chan_from_exchange.

(*
chan is idle ∨
(offer from receiver ∗ receiver's atomic update) ∨
(offer from sender ∗ sender's atomic update)
*)
