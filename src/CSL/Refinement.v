Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Abstraction.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationTheorems.
Require Import Helpers.RelationRewriting.
Require Import CSL.WeakestPre.
From iris.algebra Require Import auth frac agree gmap list.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.

(* Encoding of an abstract source program as a ghost resource, in order to
   use Iris to prove refinements. This is patterned off of the encoding used in
   iris-examples/theories/logrel examples by Timany, Krebbers, and Frumin. *)
Unset Implicit Arguments.
Set Nested Proofs Allowed.

Definition procT {OpT} := {T : Type & proc OpT T}.
Canonical Structure procTC OpT := leibnizC (@procT OpT).
Canonical Structure StateC OpT (Λ: Layer OpT) := leibnizC (State Λ).

Section ghost. 
Context {OpT: Type → Type}.
Context {Λ: Layer OpT}.


Definition tpoolUR := gmapUR nat (exclR (procTC OpT)).
Definition stateUR := optionUR (exclR (StateC _ Λ)).
Definition cfgUR := prodUR tpoolUR stateUR.
Class cfgG Σ := { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Fixpoint tpool_to_map_aux (tp: thread_pool OpT) (id: nat) : tpoolUR :=
  match tp with
  | [] => ∅
  | e :: tp' => <[id := Excl e]>(tpool_to_map_aux tp' (S id))
  end.

Definition tpool_to_map tp := tpool_to_map_aux tp O.

Definition sourceN := nroot .@ "source".

Section ghost_spec.
  Context `{cfgG Σ, invG Σ}.

  Definition tpool_mapsto {T} (j: nat) (e: proc OpT T) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl (existT _ e : procTC OpT) ]}, ε)).
  
  Definition source_state (σ: State Λ) : iProp Σ :=
    own cfg_name (◯ (∅ : tpoolUR, Some (Excl σ))).

  Definition source_inv (tp: thread_pool OpT) (σ: State Λ) : iProp Σ :=
    (∃ tp' σ', own cfg_name (● (tpool_to_map tp', Some (Excl σ')))  ∗
                 ⌜ bind_star (exec_pool Λ) tp σ σ' tp' ⌝)%I.
    
  Definition source_ctx ρ : iProp Σ :=
    inv sourceN (source_inv (fst ρ) (snd ρ)).

  Global Instance tpool_mapsto_timeless {T} j (e: proc OpT T) : Timeless (tpool_mapsto j e).
  Proof. apply _. Qed.
  Global Instance source_state_timeless σ : Timeless (source_state σ).
  Proof. apply _. Qed.
  Global Instance source_ctx_persistent ρ : Persistent (source_ctx ρ).
  Proof. apply _. Qed.

End ghost_spec.

Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Section ghost_step.
  Context `{cfgG Σ, invG Σ}.
  Context `{Inhabited Λ.(State)}.

  Lemma tpool_to_map_lookup_aux tp id j e:
    tpool_to_map_aux tp id !! (id + j) = Some (Excl e) ↔ tp !! j = Some e.
  Proof.
    revert id j; induction tp => id j //=.
    destruct j.
    * rewrite //= Nat.add_0_r lookup_insert //=.
      split; inversion 1; auto; setoid_subst; eauto.
    * rewrite //= lookup_insert_ne //=; last by lia.
      replace (id + S j) with (S id + j) by lia; eauto.
  Qed.

  Lemma tpool_to_map_lookup_aux_none tp id j:
    tpool_to_map_aux tp id !! (id + j) = None ↔ tp !! j = None.
  Proof.
    revert id j; induction tp => id j //=.
    destruct j.
    * rewrite //= Nat.add_0_r lookup_insert //=.
    * rewrite //= lookup_insert_ne //=; last by lia.
      replace (id + S j) with (S id + j) by lia; eauto.
  Qed.

  Lemma tpool_to_map_lookup tp j e:
    tpool_to_map tp !! j = Some (Excl e) ↔ tp !! j = Some e.
  Proof.
    rewrite /tpool_to_map. pose (tpool_to_map_lookup_aux tp 0 j e) => //=.
  Qed.

  Lemma tpool_to_map_lookup_none tp j:
    tpool_to_map tp !! j = None ↔ tp !! j = None.
  Proof.
    rewrite /tpool_to_map. pose (tpool_to_map_lookup_aux_none tp 0 j) => //=.
  Qed.

  Lemma tpool_to_map_lookup_excl tp j x:
    tpool_to_map tp !! j = Some x → ∃ e, x = Excl e.
  Proof.
    rewrite /tpool_to_map. generalize 0. induction tp => n //=.
    destruct (decide (j = n)); subst.
    * rewrite lookup_insert. inversion 1; setoid_subst; by eexists.
    * rewrite lookup_insert_ne //=; eauto.
  Qed.

  Lemma tpool_to_map_insert tp j e :
    j < length tp →
    tpool_to_map (<[j := e]> tp) = <[j := Excl e]> (tpool_to_map tp).
  Proof.
    intros Hlt. apply: map_eq; intros i.
    destruct (decide (i = j)); subst.
    - rewrite lookup_insert tpool_to_map_lookup list_lookup_insert //=.
    - rewrite lookup_insert_ne //=.
      destruct (decide (i < length tp)) as [Hl|Hnl].
      * efeed pose proof (lookup_lt_is_Some_2 tp) as His; first eassumption.
        destruct His as (e'&His).
        rewrite (proj2 (tpool_to_map_lookup tp i e')) //=.
        apply tpool_to_map_lookup. rewrite list_lookup_insert_ne //=.
      * efeed pose proof (lookup_ge_None_2 tp i) as Hnone; first lia.
        rewrite (proj2 (tpool_to_map_lookup_none tp i)) //=.
        apply tpool_to_map_lookup_none. rewrite list_lookup_insert_ne //=.
  Qed.
    
  Lemma tpool_to_map_length tp j e :
    tpool_to_map tp !! j = Some e → j < length tp.
  Proof.
    intros Hlookup. destruct (decide (j < length tp)) as [Hl|Hnl]; auto.
    rewrite (proj2 (tpool_to_map_lookup_none tp j)) in Hlookup; first by congruence.
    apply lookup_ge_None_2; lia.
  Qed.

  Lemma tpool_singleton_included1 tp j e :
    {[j := Excl e]} ≼ tpool_to_map tp → tpool_to_map tp !! j = Some (Excl e).
  Proof.
    intros (x&Hlookup&Hexcl)%singleton_included.
    destruct (tpool_to_map_lookup_excl tp j x) as (e'&Heq); setoid_subst; eauto.
    apply Excl_included in Hexcl; setoid_subst; auto.
  Qed.

  Lemma tpool_singleton_included2 tp j e :
    {[j := Excl e]} ≼ tpool_to_map tp → tp !! j = Some e.
  Proof.
    intros Hlookup%tpool_singleton_included1.
    apply tpool_to_map_lookup; rewrite Hlookup; eauto.
  Qed.

  Lemma source_thread_update {T T'} (e': proc OpT T') tp j (e: proc OpT T)  σ :
    j ⤇ e -∗ own cfg_name (● (tpool_to_map tp, Excl' σ))
      ==∗ j ⤇ e' ∗ own cfg_name (● (tpool_to_map (<[j := existT _ e']>tp), Excl' σ)).
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_valid_discrete_2 in Hval_pool as ((Hpool&_)%prod_included&Hval').
    apply tpool_singleton_included1 in Hpool.
    iMod (own_update_2 with "Hauth Hj") as "[Hauth Hj]".
    {
      eapply auth_update, prod_local_update_1.
      eapply singleton_local_update,
      (exclusive_local_update _ (Excl (existT _ e' : procTC OpT))); eauto.
      { econstructor. }
    }
    iFrame.
    rewrite tpool_to_map_insert //; last first.
    { eapply tpool_to_map_length; eauto. }
  Qed.

  Lemma source_state_update σ' tp σ1 σ2 :
    source_state σ1 -∗ own cfg_name (● (tpool_to_map tp, Excl' σ2))
      ==∗ source_state σ' ∗ own cfg_name (● (tpool_to_map tp, Excl' σ')).
  Proof.
    iIntros "Hstate Hauth".
    iDestruct (own_valid_2 with "Hauth Hstate") as %Hval_state.
    apply auth_valid_discrete_2 in Hval_state as ((_&Hstate)%prod_included&Hval').
    apply Excl_included in Hstate; setoid_subst.
    iMod (own_update_2 with "Hauth Hstate") as "[Hauth Hstate]".
    {
      eapply auth_update, prod_local_update_2.
      apply option_local_update, (exclusive_local_update _ (Excl σ')); econstructor.
    }
    by iFrame.
  Qed.

  Lemma ghost_step_lifting {T1 T2} E ρ j K `{LanguageCtx OpT T1 T2 Λ K}
             (e1: proc OpT T1) σ1 σ2 e2 efs:
    Λ.(exec_step) e1 σ1 σ2 (e2, efs) →
    nclose sourceN ⊆ E →
    source_ctx ρ ∗ j ⤇ K e1 ∗ source_state σ1
      ={E}=∗ j ⤇ K e2 ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ `(projT2 ef).
  Proof.
    iIntros (Hstep ?) "(#Hctx&Hj&Hstate)". rewrite /source_ctx/source_inv.
    iInv "Hctx" as (tp' σ') ">[Hauth %]" "Hclose".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    iDestruct (own_valid_2 with "Hauth Hstate") as %Hval_state.
    iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
    iMod (source_state_update σ2 with "Hstate Hauth") as "[Hstate Hauth]".
    (* TODO: allocate the new threads *)
    iMod ("Hclose" with "[Hauth]").
    { iNext. iExists (<[j := (existT T2 (K e2))]>tp'), σ2.
      iFrame. admit.
    }
    iModIntro; iFrame.
    admit.
  Admitted.

End ghost_step.
End ghost.