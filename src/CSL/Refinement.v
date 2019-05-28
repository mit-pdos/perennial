Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
From Transitions Require Import Relations.
Require Import CSL.WeakestPre CSL.Lifting.
From iris.algebra Require Import auth frac agree gmap list excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.

(* Encoding of an abstract source program as a ghost resource, in order to
   use Iris to prove refinements. This is patterned off of the encoding used in
   iris-examples/theories/logrel examples by Timany et al. *)
Global Unset Implicit Arguments.
Set Nested Proofs Allowed.

Definition procT {OpT} := {T : Type & proc OpT T}.
Canonical Structure procTC OpT := leibnizC (@procT OpT).
Canonical Structure StateC OpT (Λ: Layer OpT) := leibnizC (OpState Λ).

Section ghost.
Context {OpT: Type → Type}.
Context {Λ: Layer OpT}.


Definition tpoolUR := gmapUR nat (exclR (procTC OpT)).
Definition stateUR := optionUR (exclR (StateC _ Λ)).
Definition cfgUR := prodUR tpoolUR stateUR.

Class cfgPreG (Σ : gFunctors) :=
  { cfg_preG_inG :> inG Σ (authR cfgUR) }.
Class cfgG Σ := { cfg_inG :> inG Σ (authR cfgUR); cfg_name : gname }.

Definition cfgΣ : gFunctors :=
  #[GFunctor (authR (cfgUR))].

Instance subG_cfgPreG {Σ} :
  subG (cfgΣ) Σ → cfgPreG Σ.
Proof. solve_inG. Qed.

Fixpoint tpool_to_map_aux (tp: thread_pool OpT) (id: nat) : gmap nat (@procT OpT):=
  match tp with
  | [] => ∅
  | e :: tp' => <[id := e]>(tpool_to_map_aux tp' (S id))
  end.

Definition tpool_to_map tp := tpool_to_map_aux tp O.
Definition tpool_to_res tp := (Excl <$> (tpool_to_map tp) : tpoolUR).

Definition sourceN := nroot .@ "source".

Section ghost_spec.
  Context `{cfgG Σ, invG Σ}.

  Definition tpool_mapsto {T} (j: nat) (e: proc OpT T) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl (existT _ e : procTC OpT) ]}, ε)).

  (* ownership of this does not mean there aren't other threads not in (fst ρ) *)
  Definition source_cfg (ρ: thread_pool OpT * State Λ) : iProp Σ :=
    own cfg_name (◯ (tpool_to_res (fst ρ), Some (Excl (snd (snd ρ))))).

  Definition source_state (σ: OpState Λ) : iProp Σ :=
    own cfg_name (◯ (∅ : tpoolUR, Some (Excl σ))).

  Definition source_pool_map (tp: gmap nat ({T : Type & proc OpT T})) : iProp Σ :=
    own cfg_name (◯ (Excl <$> tp : gmap nat (exclR (procTC OpT)), ε)).

  Definition source_inv (tp: thread_pool OpT) (σ: OpState Λ) : iProp Σ :=
    (∃ tp' n σ', own cfg_name (● (tpool_to_res tp', Some (Excl σ'))) ∗
                   ⌜ bind_star (exec_pool Λ.(sem)) tp (1, σ) (Val (n, σ') tp')
                     ∧ ¬ bind_star (exec_pool Λ.(sem)) tp (1, σ) Err ⌝)%I.

  Definition source_ctx' ρ : iProp Σ :=
    inv sourceN (source_inv (fst ρ) (snd ρ)).

  Definition source_ctx : iProp Σ :=
    (∃ ρ, source_ctx' ρ)%I.

  Global Instance tpool_mapsto_timeless {T} j (e: proc OpT T) : Timeless (tpool_mapsto j e).
  Proof. apply _. Qed.
  Global Instance source_state_timeless σ : Timeless (source_state σ).
  Proof. apply _. Qed.
  Global Instance source_ctx'_persistent ρ : Persistent (source_ctx' ρ).
  Proof. apply _. Qed.
  Global Instance source_ctx_persistent : Persistent (source_ctx).
  Proof. apply _. Qed.

End ghost_spec.

Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Section ghost_step.
  Context `{invG Σ}.

  Lemma tpool_to_map_lookup_aux tp id j e:
    tpool_to_map_aux tp id !! (id + j) = Some e ↔ tp !! j = Some e.
  Proof.
    revert id j; induction tp => id j //=.
    destruct j.
    * rewrite //= Nat.add_0_r lookup_insert //=.
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
    tpool_to_map tp !! j = Some e ↔ tp !! j = Some e.
  Proof.
    rewrite /tpool_to_map. pose (tpool_to_map_lookup_aux tp 0 j e) => //=.
  Qed.

  Lemma tpool_to_map_lookup_none tp j:
    tpool_to_map tp !! j = None ↔ tp !! j = None.
  Proof.
    rewrite /tpool_to_map. pose (tpool_to_map_lookup_aux_none tp 0 j) => //=.
  Qed.

  Lemma tpool_to_res_lookup tp j e:
    tpool_to_res tp !! j = Some (Excl e) ↔ tp !! j = Some e.
  Proof.
    rewrite /tpool_to_res lookup_fmap. generalize (tpool_to_map_lookup tp j e) => Hconv.
    split.
    - destruct (tpool_to_map tp !! j); inversion 1; subst; eapply Hconv; eauto.
    - intros. rewrite (proj2 Hconv); eauto.
  Qed.

  Lemma tpool_to_res_lookup_none tp j:
    tpool_to_res tp !! j = None ↔ tp !! j = None.
  Proof.
    rewrite /tpool_to_res lookup_fmap. generalize (tpool_to_map_lookup_none tp j) => Hconv.
    split.
    -destruct (tpool_to_map tp !! j); inversion 1; subst; eapply Hconv; eauto.
    - intros. rewrite (proj2 Hconv); eauto.
  Qed.

  Lemma tpool_to_res_lookup_excl tp j x:
    tpool_to_res tp !! j = Some x → ∃ e, x = Excl e.
  Proof.
    rewrite /tpool_to_res/tpool_to_map. generalize 0. induction tp => n //=.
    destruct (decide (j = n)); subst.
    * rewrite lookup_fmap //= lookup_insert. inversion 1; setoid_subst; by eexists.
    * rewrite lookup_fmap //= lookup_insert_ne //= -lookup_fmap; eauto.
  Qed.

  Lemma tpool_to_res_insert_update tp j e :
    j < length tp →
    tpool_to_res (<[j := e]> tp) = <[j := Excl e]> (tpool_to_res tp).
  Proof.
    intros Hlt. apply: map_eq; intros i.
    destruct (decide (i = j)); subst.
    - rewrite lookup_insert tpool_to_res_lookup list_lookup_insert //=.
    - rewrite lookup_insert_ne //=.
      destruct (decide (i < length tp)) as [Hl|Hnl].
      * efeed pose proof (lookup_lt_is_Some_2 tp) as His; first eassumption.
        destruct His as (e'&His).
        rewrite (proj2 (tpool_to_res_lookup tp i e')) //=.
        apply tpool_to_res_lookup. rewrite list_lookup_insert_ne //=.
      * efeed pose proof (lookup_ge_None_2 tp i) as Hnone; first lia.
        rewrite (proj2 (tpool_to_res_lookup_none tp i)) //=.
        apply tpool_to_res_lookup_none. rewrite list_lookup_insert_ne //=.
  Qed.

  Lemma tpool_to_res_insert_snoc tp e :
    tpool_to_res (tp ++ [e]) = <[length tp := Excl e]> (tpool_to_res tp).
  Proof.
    apply: map_eq; intros i.
    destruct (decide (i = length tp)); subst.
    - rewrite lookup_insert tpool_to_res_lookup.
      rewrite lookup_app_r //= Nat.sub_diag //=.
    - rewrite lookup_insert_ne //=.
      destruct (decide (i < length tp)) as [Hl|Hnl].
      * efeed pose proof (lookup_lt_is_Some_2 tp) as His; first eassumption.
        destruct His as (e'&His).
        rewrite (proj2 (tpool_to_res_lookup tp i e')) //=.
        apply tpool_to_res_lookup. rewrite lookup_app_l //=.
      * efeed pose proof (lookup_ge_None_2 tp i) as Hnone; first lia.
        rewrite (proj2 (tpool_to_res_lookup_none tp i)) //=.
        apply tpool_to_res_lookup_none. rewrite lookup_ge_None_2 //= app_length //=; lia.
  Qed.

  Lemma tpool_to_res_length tp j e :
    tpool_to_res tp !! j = Some e → j < length tp.
  Proof.
    intros Hlookup. destruct (decide (j < length tp)) as [Hl|Hnl]; auto.
    rewrite (proj2 (tpool_to_res_lookup_none tp j)) in Hlookup; first by congruence.
    apply lookup_ge_None_2; lia.
  Qed.

  Lemma tpool_singleton_included1 tp j e :
    {[j := Excl e]} ≼ tpool_to_res tp → tpool_to_res tp !! j = Some (Excl e).
  Proof.
    intros (x&Hlookup&Hexcl)%singleton_included.
    destruct (tpool_to_res_lookup_excl tp j x) as (e'&Heq); setoid_subst; eauto.
    apply Excl_included in Hexcl; setoid_subst; auto.
  Qed.

  Lemma tpool_singleton_included2 tp j e :
    {[j := Excl e]} ≼ tpool_to_res tp → tp !! j = Some e.
  Proof.
    intros Hlookup%tpool_singleton_included1.
    apply tpool_to_res_lookup; rewrite Hlookup; eauto.
  Qed.

  Lemma tpool_map_included1 tp1 tp2 :
    Excl <$> tp1 ≼ tpool_to_res tp2 → (∀ j e, tp1 !! j = Some e → tp2 !! j = Some e).
  Proof.
    rewrite lookup_included => Hincl j e Hin.
    specialize (Hincl j). apply tpool_to_res_lookup.
    rewrite (lookup_fmap _ tp1 j) Hin //= in Hincl.
    destruct (tpool_to_res tp2 !! j) as [x|] eqn: Heq; rewrite Heq in Hincl.
    {
      destruct (tpool_to_res_lookup_excl tp2 j x) as (e'&Heq'); setoid_subst; eauto.
      apply Excl_included in Hincl; setoid_subst; eauto.
    }
    apply option_included in Hincl as [Hfalse|(?&?&?&?&?)]; congruence.
  Qed.

  Lemma tpool_to_res_lookup_case tp j:
    (tpool_to_res tp !! j = None) ∨ (∃ e, tpool_to_res tp !! j = Excl' e).
  Proof.
    rewrite /tpool_to_res.
    destruct (tpool_to_map tp !! j) as [p|] eqn:Heq; rewrite lookup_fmap Heq //=.
    * by (right; exists p).
    * by left.
  Qed.

  Lemma source_cfg_init `{cfgPreG Σ} tp (σ: OpState Λ) :
    ¬ bind_star (exec_pool Λ.(sem)) tp (1, σ) Err →
    (|={⊤}=> ∃ _ : cfgG Σ, source_ctx' (tp, σ)
                                       ∗ source_pool_map (tpool_to_map tp) ∗ source_state σ)%I.
  Proof.
    intros Hno_err.
    iMod (own_alloc (● (tpool_to_res tp, Some (Excl σ))
                       ⋅ ◯ (tpool_to_res tp, Some (Excl σ)))) as (γ) "(Hauth&Hfrag)".
    { apply @auth_both_valid; first by apply _. split; [| split].
      { reflexivity. }
      - rewrite //=. intros i.
        destruct (tpool_to_res_lookup_case tp i) as [Heq_none|(e&Heq_some)].
        * rewrite Heq_none; econstructor.
        * rewrite Heq_some; econstructor.
      - rewrite //=.
    }
    set (IN := {| cfg_name := γ |}).
    iExists IN.
    iMod (inv_alloc sourceN ⊤ (source_inv tp σ) with "[Hauth]").
    { rewrite /source_inv. iNext. iExists tp, 1, σ. iFrame "Hauth".
      iPureIntro; split; eauto. econstructor. }
    iModIntro. iFrame.
    rewrite pair_split.
    iDestruct "Hfrag" as "($&$)".
  Qed.

  Context `{cfgG Σ}.
  Context `{Inhabited Λ.(OpState)}.

  Lemma source_thread_update {T T'} (e': proc OpT T') tp j (e: proc OpT T)  σ :
    j ⤇ e -∗ own cfg_name (● (tpool_to_res tp, Excl' σ))
      ==∗ j ⤇ e' ∗ own cfg_name (● (tpool_to_res (<[j := existT _ e']>tp), Excl' σ)).
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_both_valid in Hval_pool as ((Hpool&_)%prod_included&Hval').
    apply tpool_singleton_included1 in Hpool.
    iMod (own_update_2 with "Hauth Hj") as "[Hauth Hj]".
    {
      eapply auth_update, prod_local_update_1.
      eapply singleton_local_update,
      (exclusive_local_update _ (Excl (existT _ e' : procTC OpT))); eauto.
      { econstructor. }
    }
    iFrame.
    rewrite tpool_to_res_insert_update //; last first.
    { eapply tpool_to_res_length; eauto. }
  Qed.

  Lemma source_threads_fork (efs: thread_pool OpT) tp σ :
    own cfg_name (● (tpool_to_res tp, Excl' σ))
      ==∗ ([∗ list] ef ∈ efs, ∃ j', j' ⤇ `(projT2 ef))
        ∗ own cfg_name (● (tpool_to_res (tp ++ efs), Excl' σ)).
  Proof.
    iInduction efs as [| ef efs] "IH" forall (tp).
    - rewrite /= app_nil_r /=; auto.
    - iIntros "Hown".
      iMod (own_update with "Hown") as "[Hown Hj']".
      eapply auth_update_alloc, prod_local_update_1.
      eapply (alloc_local_update (tpool_to_res tp) _ (length tp) (Excl ef)).
      { apply tpool_to_res_lookup_none, lookup_ge_None_2. reflexivity. }
      { econstructor. }
      iEval (rewrite insert_empty) in "Hj'".
      rewrite //= -assoc.
      iSplitL "Hj'".
      { iExists (length tp); destruct ef; iModIntro; eauto. }
      replace (ef :: efs) with ([ef] ++ efs) by auto.
      rewrite assoc. iApply "IH".
      rewrite tpool_to_res_insert_snoc; eauto.
  Qed.

  Lemma source_state_update σ' tp σ1 σ2 :
    source_state σ1 -∗ own cfg_name (● (tpool_to_res tp, Excl' σ2))
      ==∗ source_state σ' ∗ own cfg_name (● (tpool_to_res tp, Excl' σ')).
  Proof.
    iIntros "Hstate Hauth".
    iDestruct (own_valid_2 with "Hauth Hstate") as %Hval_state.
    apply auth_both_valid in Hval_state as ((_&Hstate)%prod_included&Hval').
    apply Excl_included in Hstate; setoid_subst.
    iMod (own_update_2 with "Hauth Hstate") as "[Hauth Hstate]".
    {
      eapply auth_update, prod_local_update_2.
      apply option_local_update, (exclusive_local_update _ (Excl σ')); econstructor.
    }
    by iFrame.
  Qed.

  Lemma source_thread_reconcile {T} tp j e x:
    j ⤇ e -∗ own cfg_name (● (tpool_to_res tp, x)) -∗ ⌜ tp !! j = Some (existT T e) ⌝.
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_both_valid in Hval_pool as ((Hpool&_)%prod_included&Hval').
    apply tpool_singleton_included1, tpool_to_res_lookup in Hpool; eauto.
  Qed.

  Lemma source_pool_map_reconcile tp1 tp2 x:
    source_pool_map tp1 -∗ own cfg_name (● (tpool_to_res tp2, x)) -∗
                    ⌜ ∀ i e, tp1 !! i = Some e → tp2 !! i = Some e ⌝.
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_both_valid in Hval_pool as ((Hpool&_)%prod_included&Hval').
    iPureIntro. eapply tpool_map_included1; eauto.
  Qed.

  Lemma source_state_reconcile σ σ' x:
    source_state σ -∗ own cfg_name (● (x, Excl' σ')) -∗ ⌜ σ = σ' ⌝.
  Proof.
    iIntros "Hstate Hauth".
    iDestruct (own_valid_2 with "Hauth Hstate") as %Hval_state.
    apply auth_both_valid in Hval_state as ((_&Hstate)%prod_included&_).
    apply Excl_included in Hstate; setoid_subst; auto.
  Qed.

  Lemma ghost_step_lifting' {T1 T2} E ρ j K `{LanguageCtx OpT T1 T2 Λ K}
             (e1: proc OpT T1) σ1 σ2 e2 efs:
    (∀ n, ∃ n', exec_step Λ.(sem) e1 (n, σ1) (Val (n', σ2) (e2, efs))) →
    nclose sourceN ⊆ E →
    source_ctx' ρ ∗ j ⤇ K e1 ∗ source_state σ1
      ={E}=∗ j ⤇ K e2 ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ (projT2 ef).
  Proof.
    iIntros (Hstep ?) "(#Hctx&Hj&Hstate)". rewrite /source_ctx/source_inv.
    iInv "Hctx" as (tp' n' σ') ">[Hauth %]" "Hclose".

    (* Reconcile view based on authoritative element *)
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    iDestruct (source_state_reconcile with "Hstate Hauth") as %Heq_state.
    setoid_subst.

    (* Update authoritative resources to simulate step *)
    iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
    iMod (source_threads_fork efs with "Hauth") as "[Hj' Hauth]".
    iMod (source_state_update σ2 with "Hstate Hauth") as "[Hstate Hauth]".
    destruct (Hstep n') as (n''&?).

    (* Restore the invariant *)
    iMod ("Hclose" with "[Hauth]").
    { iNext. iExists (<[j := (existT T2 (K e2))]>tp' ++ efs), n'', σ2.
      iFrame. intuition. iPureIntro; split; auto.

      apply bind_star_expand_r_valid.
      right. exists tp', (n', σ'); split; auto.
      apply exec_pool_equiv_alt_val.
      econstructor.
      { symmetry; eapply take_drop_middle; eauto. }
      { reflexivity. }
      { f_equal. rewrite app_comm_cons assoc; f_equal.
        erewrite <-take_drop_middle at 1; f_equal.
        { apply take_insert; reflexivity. }
        { f_equal. apply drop_insert; lia. }
        rewrite list_lookup_insert //=.
        apply lookup_lt_is_Some_1; eauto.
      }
      eapply fill_step_valid; eauto.
    }
    iModIntro; iFrame.
  Qed.

  (* Curried form is more useful, I think *)
  Lemma ghost_step_lifting {T1 T2} E j K `{LanguageCtx OpT T1 T2 Λ K}
             (e1: proc OpT T1) σ1 σ2 e2 efs:
    (∀ n, ∃ n', exec_step Λ.(sem) e1 (n, σ1) (Val (n', σ2) (e2, efs))) →
    nclose sourceN ⊆ E →
    j ⤇ K e1 -∗ source_ctx -∗ source_state σ1
      ={E}=∗ j ⤇ K e2 ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ (projT2 ef).
  Proof.
    iIntros (??) "Hj Hsrc ?".
    iDestruct "Hsrc" as (?) "Hsrc".
    iApply ghost_step_lifting'; eauto. iFrame.
  Qed.

  Lemma ghost_step_call {T1 T2} E j K `{LanguageCtx OpT T1 T2 Λ K} r σ2
             (op: OpT T1) σ1 :
    (∀ n, exec_step Λ.(sem) (Call op) (n, σ1) (Val (n, σ2) (Ret r, []))) →
    nclose sourceN ⊆ E →
    j ⤇ K (Call op) -∗ source_ctx -∗ source_state σ1
      ={E}=∗ j ⤇ K (Ret r) ∗ source_state σ2 ∗ [∗ list] ef ∈ [], ∃ j', j' ⤇ (projT2 ef).
  Proof.
    iIntros (??) "Hj Hsrc ?".
    iApply (ghost_step_lifting with "Hj Hsrc"); eauto; iFrame.
  Qed.

  Lemma ghost_step_err {T1 T2} E j K `{LanguageCtx OpT T1 T2 Λ K} (op: OpT T1) σ:
    (∀ n, exec_step Λ.(sem) (Call op) (n, σ) Err) →
    nclose sourceN ⊆ E →
    j ⤇ K (Call op) -∗ source_ctx -∗ source_state σ ={E}=∗ False.
  Proof.
    iIntros (??) "Hj Hctx Hstate".
    rewrite /source_ctx/source_inv.
    iDestruct "Hctx" as (ρ) "#Hctx".
    iInv "Hctx" as (tp' n' σ') ">[Hauth Hpure]" "Hclose".
    iDestruct "Hpure" as %(Hstep&Hnoerr).
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    iDestruct (source_state_reconcile with "Hstate Hauth") as %Heq_state.
    subst.
    exfalso. eapply Hnoerr.
    apply bind_star_expand_r_err.
    right. right. exists tp', (n', σ'); split; auto.
    apply exec_pool_equiv_alt_err.
    eapply step_atomic_error.
    { symmetry; eapply take_drop_middle; eauto. }
    { reflexivity. }
    { eapply fill_step_err; eauto. }
  Qed.

  Lemma ghost_step_lifting_puredet {T1 T2} E j K `{LanguageCtx OpT T1 T2 Λ K}
             (e1: proc OpT T1) e2 efs:
    (∀ n σ1, ∃ n', exec_step Λ.(sem) e1 (n, σ1) (Val (n', σ1) (e2, efs))) →
    nclose sourceN ⊆ E →
    source_ctx ∗ j ⤇ K e1
      ={E}=∗ j ⤇ K e2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ (projT2 ef).
  Proof.
    iIntros (Hstep ?) "(#Hctx&Hj)". iDestruct "Hctx" as (?) "Hctx". rewrite /source_ctx/source_inv.
    iInv "Hctx" as (tp' n' σ') ">[Hauth %]" "Hclose".

    (* Reconcile view based on authoritative element *)
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    setoid_subst.

    (* Update authoritative resources to simulate step *)
    iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
    iMod (source_threads_fork efs with "Hauth") as "[Hj' Hauth]".
    destruct (Hstep n' σ') as (n''&?).

    (* Restore the invariant *)
    iMod ("Hclose" with "[Hauth]").
    { iNext. iExists (<[j := (existT T2 (K e2))]>tp' ++ efs), _, _.
      iFrame. intuition. iPureIntro; split; auto.

      apply bind_star_expand_r_valid.
      right. exists tp', (n', σ'); split; auto.
      apply exec_pool_equiv_alt_val.
      econstructor.
      { symmetry; eapply take_drop_middle; eauto. }
      { reflexivity. }
      { f_equal. rewrite app_comm_cons assoc; f_equal.
        erewrite <-take_drop_middle at 1; f_equal.
        { apply take_insert; reflexivity. }
        { f_equal. apply drop_insert; lia. }
        rewrite list_lookup_insert //=.
        apply lookup_lt_is_Some_1; eauto.
      }
      eapply fill_step_valid; eauto.
    }
    iModIntro; iFrame.
  Qed.

  Lemma ghost_step_lifting_bind' {T1 T2} E j (K: T1 → proc OpT T2)
             (e1: proc OpT T1) σ1 σ2 e2 efs:
    (∀ n, ∃ n', exec_step Λ.(sem) e1 (n, σ1) (Val (n', σ2) (e2, efs))) →
    nclose sourceN ⊆ E →
    source_ctx ∗ j ⤇ Bind e1 K ∗ source_state σ1
      ={E}=∗ j ⤇ Bind e2 K ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ (projT2 ef).
  Proof.
    intros.
    iIntros "(Hsrc&Hj&?)". iDestruct "Hsrc" as (ρ) "Hsrc".
    iApply (ghost_step_lifting' E ρ j (fun x => Bind x K) with "[$]"); eauto.
  Qed.

  Lemma ghost_step_lifting_bind {T1 T2} E j (K: T1 → proc OpT T2)
             (e1: proc OpT T1) σ1 σ2 e2 efs:
    (∀ n, ∃ n', exec_step Λ.(sem) e1 (n, σ1) (Val (n', σ2) (e2, efs))) →
    nclose sourceN ⊆ E →
    j ⤇ Bind e1 K -∗ source_ctx -∗ source_state σ1
      ={E}=∗ j ⤇ Bind e2 K ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ (projT2 ef).
  Proof. iIntros. iApply ghost_step_lifting_bind'; eauto. iFrame. iAssumption. Qed.

  Lemma ghost_step_bind_ret {T1 T2 T3} E j K' `{LanguageCtx OpT T2 T3 Λ K'}
        (K: T1 → proc OpT T2) v:
    nclose sourceN ⊆ E →
    j ⤇ K' (Bind (Ret v) K) -∗ source_ctx ={E}=∗ j ⤇ K' (K v).
  Proof.
    iIntros (?) "Hj Hctx". iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&?)"; eauto.
    { intros. eexists. econstructor. }
  Qed.

  Lemma ghost_step_loop {T1 T2 T3} E j K `{LanguageCtx OpT T2 T3 Λ K}
        (body: T1 → proc OpT (LoopOutcome T1 T2)) v:
    nclose sourceN ⊆ E →
    j ⤇ K (Loop body v) -∗ source_ctx ={E}=∗ j ⤇ K (loop1 body v).
  Proof.
    iIntros (?) "Hj Hctx". iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&?)"; eauto.
    { intros. eexists. econstructor. }
  Qed.

  Lemma ghost_step_spawn {T T'} E j K `{LanguageCtx OpT unit T Λ K} (e: proc OpT T'):
    nclose sourceN ⊆ E →
    j ⤇ K (Spawn e) -∗ source_ctx
    ={E}=∗ j ⤇ K (Ret tt) ∗ (∃ j', j' ⤇ (Bind e (λ _, Unregister))).
  Proof.
    iIntros (?) "Hj Hctx". iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&H)"; eauto.
    { intros. exists (S n). econstructor.  exists (S n, σ1); split; econstructor; eauto.
      econstructor; eauto.
    }
    iModIntro. iDestruct "H" as "($&_)".
  Qed.

End ghost_step.
End ghost.

Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.
