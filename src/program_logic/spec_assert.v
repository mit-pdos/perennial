From iris.algebra Require Import auth frac agree gmap list excl.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export language.
From iris.program_logic Require Import lifting.
From Perennial.program_logic Require Export crash_lang ncinv staged_invariant.

Set Default Proof Using "Type".

(*

   Encoding of an abstract source program as a ghost resource, in order to use
   Iris to prove refinements. This encoding is based on that of the one used in
   iris-examples/theories/logrel/rules_binary.v for the logical relations proofs
   by Timany et al.

*)

Section ghost.
Context {Λ: language}.
Context {CS: crash_semantics Λ}.

(** The CMRA for the heap of the specification. *)
Definition tpoolUR : ucmraT := gmapUR nat (exclR (exprO Λ)).
Definition stateUR := optionUR (exclR (stateO Λ)).
Definition cfgUR := prodUR tpoolUR stateUR.


Class cfgPreG (Σ : gFunctors) :=
  { cfg_preG_inG :> inG Σ (authR cfgUR) ;
    cfg_preG_stagedG :> stagedG Σ}.
Class cfgG Σ := { cfg_inG :> inG Σ (authR cfgUR);
                  cfg_stagedG :> stagedG Σ;
                  cfg_name : gname }.

Definition cfgΣ : gFunctors :=
  #[GFunctor (authR cfgUR); stagedΣ].

Instance subG_cfgG {Σ} : subG cfgΣ Σ → cfgPreG Σ.
Proof. solve_inG. Qed.

Fixpoint tpool_to_map_aux (tp: list (language.expr Λ)) (id: nat) : gmap nat (language.expr Λ) :=
  match tp with
  | [] => ∅
  | e :: tp' => <[id := e]>(tpool_to_map_aux tp' (S id))
  end.

Definition tpool_to_map tp := tpool_to_map_aux tp O.
Definition tpool_to_res tp := (Excl <$> (tpool_to_map tp) : tpoolUR).

Definition sN := nroot .@ "source".
Definition sN_inv := sN.@ "base".

Section ghost_spec.
  Context `{cfgG Σ, crashG Σ, invG Σ}.

  Definition tpool_mapsto (j: nat) (e: language.expr Λ) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl e]}, ε)).

  (* ownership of this does not mean there aren't other threads not in (fst ρ) *)
  Definition source_cfg (ρ: (list (language.expr Λ)) * language.state Λ) : iProp Σ :=
    own cfg_name (◯ (tpool_to_res (fst ρ), Some (Excl (snd ρ)))).

  Definition source_state (σ: language.state Λ) : iProp Σ :=
    own cfg_name (◯ (∅ : tpoolUR, Some (Excl σ))).

  Definition source_pool_map (tp: gmap nat (language.expr Λ)) : iProp Σ :=
    own cfg_name (◯ (Excl <$> tp : tpoolUR, ε)).

  Definition source_inv r tp σ : iProp Σ :=
    (∃ s tp' σ', own cfg_name (● (tpool_to_res tp', Some (Excl σ'))) ∗
                   ⌜ erased_rsteps (CS := CS) r (tp, σ) (tp', σ') s
                     ∧ crash_safe (CS := CS) r (tp, σ) ⌝)%I.

  Definition source_ctx' r ρ : iProp Σ :=
    ncinv sN_inv (source_inv r (fst ρ) (snd ρ)).

  Definition source_ctx : iProp Σ :=
    (∃ r ρ, source_ctx' r ρ)%I.

  Global Instance tpool_mapsto_timeless j e : Timeless (tpool_mapsto j e).
  Proof. apply _. Qed.
  Global Instance source_state_timeless σ : Timeless (source_state σ).
  Proof. apply _. Qed.
  Global Instance source_ctx'_persistent r ρ : Persistent (source_ctx' r ρ).
  Proof. apply _. Qed.
  Global Instance source_ctx_persistent : Persistent (source_ctx).
  Proof. apply _. Qed.

End ghost_spec.

Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

Section ghost_step.
  Context `{invG Σ, crashG Σ, stagedG Σ}.

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
    intros (x&Hlookup&Hexcl)%singleton_included_l.
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

  Lemma source_cfg_init1 `{cfgPreG Σ} r tp0 σ0 tp σ s:
    erased_rsteps (CS := CS) r (tp0, σ0) (tp, σ) s →
    crash_safe (CS := CS) r (tp0, σ0) →
    ⊢ |={⊤}=> ∃ _ : cfgG Σ, source_ctx' r (tp0, σ0) ∗
                            source_pool_map (tpool_to_map tp) ∗
                            source_state σ ∗
                            <disc> |C={⊤}_0=> (source_inv r tp0 σ0).
  Proof.
    intros Herased Hno_err.
    iMod (own_alloc (● (tpool_to_res tp, Some (Excl σ))
                       ⋅ ◯ (tpool_to_res tp, Some (Excl σ)))) as (γ) "(Hauth&Hfrag)".
    { apply @auth_both_valid_discrete; first by apply _. split; [| split].
      { reflexivity. }
      - rewrite //=. intros i.
        destruct (tpool_to_res_lookup_case tp i) as [Heq_none|(e&Heq_some)].
        * rewrite Heq_none; econstructor.
        * rewrite Heq_some; econstructor.
      - rewrite //=.
    }
    set (IN := {| cfg_name := γ |}).
    iExists IN.
    iMod (ncinv_alloc sN_inv ⊤ (source_inv r tp0 σ0) with "[Hauth]") as "(#Hinv&Hcfupd)".
    { rewrite /source_inv. iNext. iExists s,tp, σ. iFrame "Hauth".
      iPureIntro; split; eauto. }
    iModIntro. iFrame.
    rewrite pair_split.
    iDestruct "Hfrag" as "($&$)". iFrame "Hinv".
    iModIntro.
    iMod (cfupd_weaken_all with "[Hcfupd]") as "H"; eauto.
    iDestruct "H" as ">$". eauto.
  Qed.

  Lemma source_cfg_init2 `{cfgPreG Σ} r tp σ :
    crash_safe (CS := CS) r (tp, σ) →
    ⊢ |={⊤}=> ∃ _ : cfgG Σ, source_ctx' r (tp, σ) ∗
                            source_pool_map (tpool_to_map tp) ∗
                            source_state σ ∗
                            <disc> |C={⊤}_0=> (source_inv r tp σ).
  Proof.
    intros Hno_err.
    iApply source_cfg_init1; eauto.
    { econstructor. econstructor. }
  Qed.

  Context `{cfgG Σ}.
  Context `{Inhabited (state Λ)}.

  Lemma source_pool_singleton e:
    source_pool_map (tpool_to_map [e]) -∗ 0 ⤇ e.
  Proof.
    rewrite /source_pool_map/tpool_to_map/tpool_to_map_aux/tpool_mapsto.
    by rewrite fmap_insert fmap_empty insert_empty.
  Qed.

  Lemma source_thread_update e' tp j e σ :
    j ⤇ e -∗ own cfg_name (● (tpool_to_res tp, Excl' σ))
      ==∗ j ⤇ e' ∗ own cfg_name (● (tpool_to_res (<[j := e']>tp), Excl' σ)).
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_both_valid_discrete in Hval_pool as ((Hpool&_)%prod_included&Hval').
    apply tpool_singleton_included1 in Hpool.
    iMod (own_update_2 with "Hauth Hj") as "[Hauth Hj]".
    {
      eapply auth_update, prod_local_update_1.
      eapply singleton_local_update,
      (exclusive_local_update _ (Excl e')); eauto.
      { econstructor. }
    }
    iFrame.
    rewrite tpool_to_res_insert_update //; last first.
    { eapply tpool_to_res_length; eauto. }
  Qed.

  Lemma source_threads_fork efs tp σ :
    own cfg_name (● (tpool_to_res tp, Excl' σ))
      ==∗ ([∗ list] ef ∈ efs, ∃ j', j' ⤇ ef)
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
      { iExists (length tp); iModIntro; eauto. }
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
    apply auth_both_valid_discrete in Hval_state as ((_&Hstate)%prod_included&Hval').
    apply Excl_included in Hstate; setoid_subst.
    iMod (own_update_2 with "Hauth Hstate") as "[Hauth Hstate]".
    {
      eapply auth_update, prod_local_update_2.
      apply option_local_update, (exclusive_local_update _ (Excl σ')); econstructor.
    }
    by iFrame.
  Qed.

  Lemma source_thread_reconcile tp j e x:
    j ⤇ e -∗ own cfg_name (● (tpool_to_res tp, x)) -∗ ⌜ tp !! j = Some e ⌝.
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_both_valid_discrete in Hval_pool as ((Hpool&_)%prod_included&Hval').
    apply tpool_singleton_included1, tpool_to_res_lookup in Hpool; eauto.
  Qed.

  Lemma source_pool_map_reconcile tp1 tp2 x:
    source_pool_map tp1 -∗ own cfg_name (● (tpool_to_res tp2, x)) -∗
                    ⌜ ∀ i e, tp1 !! i = Some e → tp2 !! i = Some e ⌝.
  Proof.
    iIntros "Hj Hauth".
    iDestruct (own_valid_2 with "Hauth Hj") as %Hval_pool.
    apply auth_both_valid_discrete in Hval_pool as ((Hpool&_)%prod_included&Hval').
    iPureIntro. eapply tpool_map_included1; eauto.
  Qed.

  Lemma source_state_reconcile σ σ' x:
    source_state σ -∗ own cfg_name (● (x, Excl' σ')) -∗ ⌜ σ = σ' ⌝.
  Proof.
    iIntros "Hstate Hauth".
    iDestruct (own_valid_2 with "Hauth Hstate") as %Hval_state.
    apply auth_both_valid_discrete in Hval_state as ((_&Hstate)%prod_included&_).
    apply Excl_included in Hstate; setoid_subst; auto.
  Qed.

  Lemma ghost_step_lifting' E r ρ j K `{LanguageCtx Λ K} e1 σ1 κ σ2 e2 efs:
    language.prim_step e1 σ1 κ e2 σ2 efs →
    nclose sN_inv ⊆ E →
    source_ctx' r ρ ∗ j ⤇ K e1 ∗ source_state σ1
      -∗ |NC={E}=> j ⤇ K e2 ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ ef.
  Proof.
    iIntros (Hstep ?) "(#Hctx&Hj&Hstate)". rewrite /source_ctx/source_inv.
    iInv "Hctx" as (s' tp' σ') ">[Hauth %]" "Hclose".

    (* Reconcile view based on authoritative element *)
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    iDestruct (source_state_reconcile with "Hstate Hauth") as %Heq_state.
    setoid_subst.

    (* Update authoritative resources to simulate step *)
    iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
    iMod (source_threads_fork efs with "Hauth") as "[Hj' Hauth]".
    iMod (source_state_update σ2 with "Hstate Hauth") as "[Hstate Hauth]".

    (* Restore the invariant *)
    iMod ("Hclose" with "[Hauth]").
    { iNext. iExists s', (<[j := K e2]>tp' ++ efs), σ2.
      iFrame. intuition. iPureIntro; split; auto.
      eapply erased_rsteps_r_1; eauto.
      eapply fill_step in Hstep.
      econstructor. econstructor; eauto.
      - f_equal. symmetry. eapply take_drop_middle; eauto.
      - f_equal. rewrite app_comm_cons assoc; f_equal.
        erewrite <-take_drop_middle at 1; f_equal.
        { apply take_insert; reflexivity. }
        { f_equal. apply drop_insert_gt; lia. }
        rewrite list_lookup_insert //=.
        apply lookup_lt_is_Some_1; eauto.
      }
    iModIntro; iFrame.
  Qed.

  (* Curried form is more useful, I think *)
  Lemma ghost_step_lifting E j K `{LanguageCtx Λ K} e1 σ1 κ σ2 e2 efs:
    language.prim_step e1 σ1 κ e2 σ2 efs →
    nclose sN_inv ⊆ E →
    j ⤇ K e1 -∗ source_ctx -∗ source_state σ1
      -∗ |NC={E}=> j ⤇ K e2 ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ ef.
  Proof.
    iIntros (??) "Hj Hsrc ?".
    iDestruct "Hsrc" as (??) "Hsrc".
    iApply ghost_step_lifting'; eauto. iFrame.
  Qed.

  Lemma ghost_step_stuck E j K `{LanguageCtx Λ K} e σ:
    stuck e σ →
    nclose sN_inv ⊆ E →
    j ⤇ K e -∗ source_ctx -∗ source_state σ -∗ |NC={E}=> False.
  Proof.
    iIntros (Hstuck ?) "Hj Hctx Hstate".
    assert (stuck (K e) σ) as Hstuck'.
    { destruct Hstuck as (?&?). split.
      - apply fill_not_val; auto.
      - apply irreducible_fill; auto.
    }
    clear Hstuck.
    rewrite /source_ctx/source_inv.
    iDestruct "Hctx" as (? ρ) "#Hctx".
    iInv "Hctx" as (? tp' σ') ">[Hauth Hpure]" "Hclose".
    iDestruct "Hpure" as %(Hstep&Hnoerr).
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    iDestruct (source_state_reconcile with "Hstate Hauth") as %Heq_state.
    subst.
    exfalso. rewrite /crash_safe in Hnoerr.
    eapply not_not_stuck in Hstuck'.
    eapply Hstuck', Hnoerr; eauto.
    by eapply elem_of_list_lookup_2.
  Qed.

  Lemma ghost_step_stuck_det E j K `{LanguageCtx Λ K} e:
    (∀ σ, stuck e σ) →
    nclose sN_inv ⊆ E →
    j ⤇ K e -∗ source_ctx -∗ |NC={E}=> False.
  Proof.
    iIntros (Hstuck ?) "Hj Hctx".
    assert (∀ σ, stuck (K e) σ) as Hstuck'.
    { intros σ. edestruct Hstuck as (?&?). split.
      - apply fill_not_val; auto.
      - apply irreducible_fill; eauto.
    }
    clear Hstuck.
    rewrite /source_ctx/source_inv.
    iDestruct "Hctx" as (? ρ) "#Hctx".
    iInv "Hctx" as (? tp' σ') ">[Hauth Hpure]" "Hclose".
    iDestruct "Hpure" as %(Hstep&Hnoerr).
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    subst.
    exfalso. rewrite /crash_safe in Hnoerr.
    eapply not_not_stuck in Hstuck'.
    eapply Hstuck', Hnoerr; eauto.
    by eapply elem_of_list_lookup_2.
  Qed.

  Lemma ghost_step_lifting_puredet E j K `{LanguageCtx Λ K} e1 e2 efs:
    (∀ σ1, ∃ κ, language.prim_step e1 σ1 κ e2 σ1 efs) →
    nclose sN_inv ⊆ E →
    source_ctx ∗ j ⤇ K e1
      -∗ |NC={E}=> j ⤇ K e2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ ef.
  Proof.
    iIntros (Hstep ?) "(#Hctx&Hj)". iDestruct "Hctx" as (??) "Hctx". rewrite /source_ctx/source_inv.
    iInv "Hctx" as (? tp' σ') ">[Hauth %]" "Hclose".

    (* Reconcile view based on authoritative element *)
    iDestruct (source_thread_reconcile with "Hj Hauth") as %Heq_thread.
    setoid_subst.

    (* Update authoritative resources to simulate step *)
    iMod (source_thread_update (K e2) with "Hj Hauth") as "[Hj Hauth]".
    iMod (source_threads_fork efs with "Hauth") as "[Hj' Hauth]".


    iMod ("Hclose" with "[Hauth]").
    { iNext. iExists _, (<[j := K e2]>tp' ++ efs), _.
      iFrame. intuition. iPureIntro; split; auto.
      eapply erased_rsteps_r_1; eauto.
      edestruct Hstep as (?&Hstep').
      eapply fill_step in Hstep'.
      econstructor. econstructor; eauto.
      - f_equal. symmetry. eapply take_drop_middle; eauto.
      - f_equal. rewrite app_comm_cons assoc; f_equal.
        erewrite <-take_drop_middle at 1; f_equal.
        { apply take_insert; reflexivity. }
        { f_equal. apply drop_insert_gt; lia. }
        rewrite list_lookup_insert //=.
        apply lookup_lt_is_Some_1; eauto.
      }
    iModIntro; iFrame.
  Qed.

  (*
  Lemma ghost_step_lifting_bind' {T1 T2} E j (K: T1 → proc OpT T2)
             (e1: proc OpT T1) σ1 σ2 e2 efs:
    (∀ n, ∃ n', exec_step Λ.(sem) e1 (n, σ1) (Val (n', σ2) (e2, efs))) →
    nclose sN_inv ⊆ E →
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
    nclose sN_inv ⊆ E →
    j ⤇ Bind e1 K -∗ source_ctx -∗ source_state σ1
      ={E}=∗ j ⤇ Bind e2 K ∗ source_state σ2 ∗ [∗ list] ef ∈ efs, ∃ j', j' ⤇ (projT2 ef).
  Proof. iIntros. iApply ghost_step_lifting_bind'; eauto. iFrame. iAssumption. Qed.

  Lemma ghost_step_bind_ret {T1 T2 T3} E j K' `{LanguageCtx OpT T2 T3 Λ K'}
        (K: T1 → proc OpT T2) v:
    nclose sN_inv ⊆ E →
    j ⤇ K' (Bind (Ret v) K) -∗ source_ctx ={E}=∗ j ⤇ K' (K v).
  Proof.
    iIntros (?) "Hj Hctx". iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&?)"; eauto.
    { intros. eexists. econstructor. }
  Qed.

  Lemma ghost_step_loop {T1 T2 T3} E j K `{LanguageCtx OpT T2 T3 Λ K}
        (body: T1 → proc OpT (LoopOutcome T1 T2)) v:
    nclose sN_inv ⊆ E →
    j ⤇ K (Loop body v) -∗ source_ctx ={E}=∗ j ⤇ K (loop1 body v).
  Proof.
    iIntros (?) "Hj Hctx". iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&?)"; eauto.
    { intros. eexists. econstructor. }
  Qed.

  Lemma ghost_step_spawn {T T'} E j K `{LanguageCtx OpT unit T Λ K} (e: proc OpT T'):
    nclose sN_inv ⊆ E →
    j ⤇ K (Spawn e) -∗ source_ctx
    ={E}=∗ j ⤇ K (Ret tt) ∗ (∃ j', j' ⤇ (Bind e (λ _, Unregister))).
  Proof.
    iIntros (?) "Hj Hctx". iMod (ghost_step_lifting_puredet with "[Hj Hctx]") as "($&H)"; eauto.
    { intros. exists (S n). econstructor.  exists (S n, σ1); split; econstructor; eauto.
      econstructor; eauto.
    }
    iModIntro. iDestruct "H" as "($&_)".
  Qed.
   *)

End ghost_step.
End ghost.

Notation "j ⤇ e" := (tpool_mapsto j e) (at level 20) : bi_scope.

