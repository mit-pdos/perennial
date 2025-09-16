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
Context `{!ghost_mapG Σ nat unit}.
Context `{!ghost_mapG Σ nat V}.
Context `{!tokenG Σ}.

Import chanstate.
(* XXX: this is actually false. Counterexample:
   send(0); send(1) || assert(recv() == 0);
   The assert can fail with `chan_send/recv_spec`
   but should be guaranteed to succeed by `goal_chan_send/goal_recv_spec`.
   The first R fulfil's send(0)'s postcondition, then the next send starts, and
   the first recevie waits until it gets send(1)'s precondition.
*)
Lemma fact :
  ⊢ |={⊤}=>
        ∃ ρ own_chan,
  own_chan (chanstate.mk [] 0) ∗
  □ (∀ v Φ, goal_send_spec own_chan v Φ -∗ chan_send_spec ρ v Φ) ∗
  □ (∀ Φ, goal_receive_spec own_chan Φ -∗ chan_receive_spec ρ Φ).
Proof.
  iMod (ghost_var_alloc (chanstate.mk [] 0)) as (γ) "[H Hc]".
  iMod (token_alloc) as (γsender) "Hsender".
  iMod (token_alloc) as (γreceiver) "Hreceiver".
  iMod (token_alloc) as (γcosender) "Hcosender".
  iMod (token_alloc) as (γcoreceiver) "Hcoreceiver".
  iMod (ghost_map_alloc (∅ : gmap nat V)) as (γsend) "[Hsend● _]".
  iMod (ghost_map_alloc (∅ : gmap nat unit)) as (γreceive) "[Hreceive● _]".
  set (own_sender := token γsender).
  set (own_receiver := token γreceiver).
  set (own_chan (s : chanstate.t V) := ghost_var γ (1/2) s).
  set (Sd (v : V) := (∃ n, n ↪[γsend]□ v ∗ (n + 1) ↪[γreceive] ())%I).
  set (Rv := (∃ n, n ↪[γsend]□ () ∗ (n + 1) ↪[γreceive] ())%I).

  iMod (inv_alloc (nroot.@"chan") _ (
            ∃ st,
              let sendm := (map_seq 0 st.(sent)) in
              let recvm := (map_seq 0 (replicate st.(received) tt)) in
              "Hoc" ∷ own_chan st ∗

              "Hsend●" ∷ ghost_map_auth γsend (1/2) sendm ∗
              "Hreceive●" ∷ ghost_map_auth γreceive (1/2) recvm ∗

              "Hsend" ∷ (("Hcosender" ∷ token γcosender ∗
                          "Hsend●2" ∷ ghost_map_auth γsend (1/2) sendm
                         ) ∨
                         token γsender
                ) ∗
              "Hreceiver" ∷ (("Hcoreceiver" ∷ token γcoreceiver ∗
                              "Hreceive●2" ∷ ghost_map_auth γreceive (1/2) recvm
                             ) ∨
                             token γreceiver
                )
          )%I with "[-H Hsender Hreceiver]") as "#Hinv".
  { iNext. iFrame.
    iDestruct "Hsend●" as "[Hs $]". iDestruct "Hreceive●" as "[Hr $]". simpl.
    iSplitL "Hs Hcosender".
    { iLeft. iFrame. }
    { iLeft. iFrame. }
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
    2:{ iCombine "Hsender Hbad" gives %[]. }
    iNamed "HH". iRename "Hsender" into "Hsender_inv".
    iDestruct "Hau" as "(% & Hoc & Hau)".
    iCombine "Hoc_inv Hoc" gives %[_ ->].
    iMod (ghost_var_update_2 with "Hoc Hoc_inv") as "[Hoc Hoc_inv]".
    { compute_done. }
    iSpecialize ("Hau" with "[$Hoc]").
    iCombine "Hsend●_inv Hsend●2" as "Hsent●".
    iMod (ghost_map_insert (length s.(sent)) v with "Hsent●") as "[[Hsend●_inv Hsend●2] Hstok]".
    { rewrite lookup_map_seq_None. lia. }
    iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]").
    { iNamed "Hi". iFrame "Hoc_inv ∗%". rewrite map_seq_snoc /=. iFrame. }


    (*
    iMod (mono_list_auth_own_update (st.(sent) ++ [v]) with "Hsent●") as "[[Hsent● Hsent_inv] #Hsent_lb]".
    { apply prefix_app_r. done. }
    iDestruct "Hau" as "(% & Hoc & Hau)".
    iCombine "Hoc_inv Hoc" gives %[_ ->].
    iMod (ghost_var_update_2 with "Hoc Hoc_inv") as "[Hoc Hoc_inv]".
    { rewrite Qp.half_half //. }
    iSpecialize ("Hau" with "[$Hoc]").
    iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]").
    { iNamed "Hi". iFrame "Hoc_inv ∗". iRight. iFrame. }
    iMod "Hau". iModIntro.
    iSplitR.
    {
      iExists _. iApply (mono_list_idx_own_get (length s.(sent)) with "[$]").
      rewrite lookup_app_r //. rewrite Nat.sub_diag //.
    }
    iIntros "HRv".
    iMod "Hau". iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[] Hi") as "Hi".
    { admit. } (* lc *)
    iMod (lc_fupd_elim_later with "[] Hau") as "Hau".
    { admit. } (* lc *)
    iNamed "HRv". *)
    (* Maintain [own_unused_rtok] for every position >= the current received
       count. When idle, have [is_used_rtok] for ever position < recv count.
       Receiver passes [own_unused_rtok ∗ smaller is_used_rtoks] to sender; this
       helps the sender conclude that the position of its append has been
       received.

       However, in order to get [own_receiver] back, must prove [is_used_rtok];
       but, we can't do that receiver gave away [own_used_rtok] to sender. And
       indeed, the sender might never even get to the step in which that fupd
       runs.

       But that's actually kind-of OK. We can have the receiver "swap" with the
       sender, and start using [own_unused_stok] for the tokens.

       When receiver is idle, say with received = 5, it has
       witnesses: [WA 1; WB 2; WA 3; WB 4]
       ownership: [A 5; B 6; A 7; ...]
       It gets (A 5) locally. Sends (A 5) to sender. From the sender, to gets
       (∃ r, if r is even then B r ∗ WA (r - 1) else A r ∗ WB (r - 1))

       When receiver is idle with (received=5), invariant owns:
         is_lb_E 4 ∗ own_O 5 ∗ own_received (1) 5.
       By putting in [own_receiver], proof gets:
         is_lb_E 4 ∗ own_O 5 ∗ own_received (1/2) 6.
       Passes [own_O 5] to sender, so have only:
         is_lb_E 4 ∗ is_lb_O 5 ∗ own_received (1/2) 6.
       From the sender, it gets Sd which is:
         ∃ s, (if s is even then (is_lb_O (s-1) ∗ own_E s) else (is_lb_E (s-1) ∗ own_O s)) ∗
              s elts are sent.

       Need to end up with (is_sent 6 ∗ own_E 6 ∗ is_lb_O 5).
       Case 1, s is odd. Then
         is_lb_E (s-1) ∗ own_O s ∗ is_lb_E 4 ∗ is_lb_O 5 ∗ own_received (1/2) 6
         s ≥ 5. Doesn't help with much, this (own_O s) is just like what we gave away.
       Case 2, s is even. Then (is_lb_O (s-1) ∗ own_E s ∗ is_sent s).
         So, s ≥ 4.

      Better starting point might be the failed (1/5) commit plan. The challenge
      there will be incrementing commit.

     *)

    (*
       S R
       \ /
        \
       / \
       S R
       \ /
        \
       / \
       S R *)
Abort.


End proof.
End unbuf_chan_from_exchange.
