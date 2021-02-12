From iris.algebra Require Import excl agree gmap lib.excl_auth gmultiset.
From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants ghost_var.
From iris.heap_lang Require Export notation lang.
From iris.heap_lang Require Import proofmode.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".

(** This is an experiment for "mover-style reasoning" in Iris.
We assume send and receive axioms based on a global view of all messages
in the network (own_network).

Then on top of that we prove specs about a "ghost network view" `own_gnetwork`
where the physical send and receive to *not* involve ownership of `own_gnetwork`;
instead they involve a "difference token": `gnetwork_diff m` witnesses that `m`
is in the logical network but not in the physical network, and that we own
that message.
`own_gnetwork` is only needed for "logically" receiving/sending messages,
which is a view shift and not tied to any physical action.
*)

Class netG Σ := NetG {
  net_msgsG :> inG Σ (authR (gmultisetUR valO));
  net_ghostG :> ghost_varG Σ (gmultiset val);
}.

Section movers.
  Context `{!heapG Σ, !netG Σ}.

  Definition message := positive.
  
  Definition network_state := gmultiset val.
  
  Axiom own_network : forall (γ:gname) (s:network_state), iProp Σ.
  Axiom own_network_timeless : forall (γ:gname) (s:network_state), Timeless (own_network γ s).
  Existing Instance own_network_timeless.

  Parameter send_pkt : val.
  Axiom send_axiom : forall s E γ (v : val) (ns:network_state),
      {{{ own_network γ ns }}}
        send_pkt v @ s; E
      {{{ RET #(); own_network γ (ns ⊎ {[ v ]}) }}}.

  Axiom send_pkt_atomic : forall a v, Atomic a (send_pkt v).
  Existing Instance send_pkt_atomic.

  Parameter recv_pkt : val.
  Axiom recv_axiom : forall s E γ (ns:network_state),
      {{{ own_network γ ns }}}
        recv_pkt #() @ s; E
      {{{ (v:val), RET v; (⌜v = NONEV⌝ ∗ own_network γ ns )
                          ∨ (∃ m, ⌜m ∈ ns ∧ v = SOMEV m⌝ ∗ own_network γ (ns ∖ {[m]}))
      }}}.

  Axiom recv_pkt_atomic : forall a v, Atomic a (recv_pkt v).
  Existing Instance recv_pkt_atomic.

  (* Assume well-known network ghost names. *)
  Context (γpnet γgdiff γgnet : gname).
  Let N := nroot .@ "mover_network".

  Definition network_inv : iProp Σ :=
    ∃ net_phys net_ghost,
      own_network γpnet net_phys ∗
      own γgdiff (● net_ghost ⋅ ◯ net_phys) ∗
      ghost_var γgnet (1/2) net_ghost.
  Definition network_ctx : iProp Σ := inv N network_inv.

  (* In a real library, these would be [Definition] and we would seal them. *)
  Notation own_gnetwork ns := (ghost_var γgnet (1/2) ns).
  Notation gnetwork_diff m := (own γgdiff (◯ ({[ m ]} : gmultiset val))).

  Local Lemma recv_mkdiff (net_phys net_ghost : gmultiset val) (m : val) :
    m ∈ net_phys →
    own γgdiff (● net_ghost ⋅ ◯ net_phys) ==∗
    own γgdiff (● net_ghost ⋅ ◯ (net_phys ∖ {[ m ]})) ∗ own γgdiff (◯ {[ m ]}).
  Proof.
    iIntros (?) "[Hauth Hfrag]". rewrite own_op. iFrame "Hauth".
    rewrite -own_op -auth_frag_op gmultiset_op.
    replace (net_phys ∖ {[m]} ⊎ {[m]}) with net_phys; first done.
    rewrite [_ ⊎ _]comm -gmultiset_disj_union_difference' //.
  Qed.

  Lemma recv_phys :
    network_ctx -∗
    {{{ True }}}
      recv_pkt #()
    {{{ (v:val), RET v; (⌜v = NONEV⌝ ∨
      (∃ (m:val), ⌜v = SOMEV m⌝ ∗ gnetwork_diff m)) }}}.
  Proof.
    iIntros "#Hctx" (Φ) "_ !# HΦ".
    iInv "Hctx" as (net_phys net_ghost) "(>Hpnet & >Hgdiff & >Hgnet)".
    iApply (recv_axiom with "Hpnet"). iIntros "!>" (v) "[Hret|Hret]".
    { iDestruct "Hret" as (->) "Hpnet". iIntros "!>". iSplitR "HΦ".
      - iNext. iExists _, _. iFrame.
      - iApply "HΦ". eauto. }
    iDestruct "Hret" as (m [Hm ->]) "Hpnet".
    iMod (recv_mkdiff with "Hgdiff") as "[Hgdiff Hgtok]"; first done.
    iIntros "!>". iSplitR "HΦ Hgtok".
    - iNext. iExists _, _. iFrame.
    - iApply "HΦ". eauto.
  Qed.

  Local Lemma recv_elimdiff (net_phys net_ghost : gmultiset val) (m : val) :
    own γgdiff (● net_ghost ⋅ ◯ net_phys) -∗ own γgdiff (◯ ({[ m ]} : gmultiset val)) ==∗
    ⌜m ∈ net_ghost⌝ ∗ own γgdiff (● (net_ghost ∖ {[ m ]}) ⋅ ◯ net_phys).
  Proof.
    iIntros "Hboth Hfrag". iCombine "Hboth Hfrag" as "Hboth".
    rewrite -assoc -auth_frag_op gmultiset_op.
    iDestruct (own_valid with "Hboth") as
      %[Hincl%gmultiset_included _]%auth_both_valid_discrete.
    assert (m ∈ net_ghost).
    { apply gmultiset_elem_of_singleton_subseteq.
      etrans; last eassumption. apply gmultiset_disj_union_subseteq_r. }
    iMod (own_update with "Hboth") as "$"; last done.
    apply auth_update, gmultiset_local_update.
    rewrite {1}(gmultiset_disj_union_difference' m net_ghost) //.
    multiset_solver.
  Qed.

  Lemma recv_log E ns m :
    ↑N ⊆ E →
    network_ctx -∗
    gnetwork_diff m -∗
    own_gnetwork ns -∗
    |={E}=> ⌜m ∈ ns⌝ ∗ own_gnetwork (ns ∖ {[ m ]}).
  Proof.
    iIntros (?) "#Hctx Hgtok Hgnetc".
    iInv "Hctx" as (net_phys net_ghost) "(>Hpnet & >Hgdiff & >Hgnet)".
    iDestruct (ghost_var_agree with "Hgnetc Hgnet") as %->.
    iMod (ghost_var_update_halves with "Hgnetc Hgnet") as "[Hgnetc Hgnet]".
    iMod (recv_elimdiff with "Hgdiff Hgtok") as (?) "Hgdiff".
    iIntros "!>". iSplitR "Hgnetc".
    - iNext. iExists _, _. iFrame.
    - eauto with iFrame.
  Qed.

  Local Lemma send_mkdiff (net_phys net_ghost : gmultiset val) m :
    own γgdiff (● net_ghost ⋅ ◯ net_phys) ==∗
    own γgdiff (● (net_ghost ⊎ ({[ m ]} : gmultiset val)) ⋅ ◯ net_phys) ∗ own γgdiff (◯ ({[ m ]} : gmultiset val)).
  Proof.
    iIntros "Hboth". rewrite -own_op -assoc -auth_frag_op gmultiset_op.
    iMod (own_update with "Hboth") as "$"; last done.
    apply auth_update, gmultiset_local_update.
    multiset_solver.
 Qed.

  Lemma send_log E ns m :
    ↑N ⊆ E →
    network_ctx -∗
    own_gnetwork ns -∗
    |={E}=> gnetwork_diff m ∗ own_gnetwork (ns ⊎ {[ m ]}).
  Proof.
    iIntros (?) "#Hctx Hgnetc".
    iInv "Hctx" as (net_phys net_ghost) "(>Hpnet & >Hgdiff & >Hgnet)".
    iDestruct (ghost_var_agree with "Hgnetc Hgnet") as %->.
    iMod (ghost_var_update_halves with "Hgnetc Hgnet") as "[Hgnetc Hgnet]".
    iMod (send_mkdiff with "Hgdiff") as "[Hgdiff Hgtok]".
    iIntros "!>". iSplitR "Hgnetc Hgtok".
    - iNext. iExists _, _. iFrame.
    - eauto with iFrame.
  Qed.

  Local Lemma send_elimdiff (net_phys net_ghost : gmultiset val) m :
    own γgdiff (● net_ghost ⋅ ◯ net_phys) -∗ own γgdiff (◯ {[ m ]}) ==∗
    own γgdiff (● net_ghost ⋅ ◯ (net_phys ⊎ {[ m ]})).
  Proof.
    iIntros "Hboth Hfrag". iCombine "Hboth Hfrag" as "Hboth".
    rewrite -assoc -auth_frag_op gmultiset_op. done.
  Qed.

  Lemma send_phys (m : val) :
    network_ctx -∗
    {{{ gnetwork_diff m }}}
      send_pkt m
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hctx" (Φ) "!# Hgtok HΦ".
    iInv "Hctx" as (net_phys net_ghost) "(>Hpnet & >Hgdiff & >Hgnet)".
    iApply (send_axiom with "Hpnet").
    iIntros "!> Hpnet".
    iMod (send_elimdiff with "Hgdiff Hgtok") as "Hgdiff".
    iIntros "!>". iSplitR "HΦ".
    - iNext. iExists _, _. iFrame.
    - iApply "HΦ". eauto.
  Qed.

End movers.
