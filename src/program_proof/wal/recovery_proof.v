From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.program_proof Require Import wal.circ_proof_crash.
From Perennial.goose_lang Require Import crash_modality.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.
Context `{!crashG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Theorem wp_MkLog_init d (bs: list Block) :
  {{{ 0 d↦∗ repeat block0 513 ∗
      513 d↦∗ bs ∗
      P (log_state.mk (list_to_map (imap (λ i x, (513 + Z.of_nat i, x)) bs)) [(U64 0, [])] 0 0)  }}}
    MkLog #d
  {{{ γ l, RET #l; is_wal P l γ }}}.
Proof.
Admitted.

Set Nested Proofs Allowed.
Lemma diskEnd_is_get_at_least (γ: circ_names) q (z: Z):
  diskEnd_is γ q z ==∗ diskEnd_is γ q z ∗ diskEnd_at_least γ z.
Proof.
  iIntros "(%&Hfm)". by iMod (fmcounter.fmcounter_get_lb with "[$]") as "($&$)".
Qed.

Lemma start_is_get_at_least (γ: circ_names) q (z: u64):
  start_is γ q z ==∗ start_is γ q z ∗ start_at_least γ z.
Proof.
  iIntros "Hfm". by iMod (fmcounter.fmcounter_get_lb with "[$]") as "($&$)".
Qed.

Existing Instance own_into_crash.

Definition log_crash_to σ diskEnd_txn_id :=
  set log_state.durable_lb (λ _, diskEnd_txn_id)
      (set log_state.txns (take diskEnd_txn_id) σ).

Lemma crash_to_diskEnd_S γ cs σ diskEnd_txn_id installed_txn_id :
  is_durable_txn γ cs σ.(log_state.txns) diskEnd_txn_id  σ.(log_state.durable_lb) -∗
  is_durable γ cs σ.(log_state.txns) installed_txn_id diskEnd_txn_id -∗
  ⌜relation.denote log_crash σ (log_crash_to σ (S diskEnd_txn_id)) tt⌝.
Proof.
  iNamed 1.
  rewrite /is_durable.
  iNamed 1.
  iPureIntro.
  simpl.
  eexists _ (S diskEnd_txn_id); simpl; monad_simpl.
  constructor.
  split; try lia.
  eapply is_highest_txn_bound; eauto.
Qed.

Lemma crash_to_diskEnd γ cs σ diskEnd_txn_id installed_txn_id :
  is_durable_txn γ cs σ.(log_state.txns) diskEnd_txn_id  σ.(log_state.durable_lb) -∗
  is_durable γ cs σ.(log_state.txns) installed_txn_id diskEnd_txn_id -∗
  ⌜relation.denote log_crash σ (log_crash_to σ (diskEnd_txn_id)) tt⌝.
Proof.
  iNamed 1.
  rewrite /is_durable.
  iNamed 1.
  iPureIntro.
  simpl.
  eexists _ (diskEnd_txn_id); simpl; monad_simpl.
  constructor.
  split; try lia.
  efeed pose proof (is_highest_txn_bound Hend_txn). lia.
Qed.

Ltac iPersist H :=
  let H' := (eval cbn in (String.append "#" H)) in
  iDestruct H as H'.

Instance is_installed_Durable γ d txns txn_id :
  IntoCrash (is_installed_read γ d txns txn_id)
            (λ _, is_installed_read γ d txns txn_id).
Proof. apply _. Qed.

Lemma concat_mono {A: Type} (l1 l2: list (list A)):
  incl l1 l2 →
  incl (concat l1) (concat l2).
Proof. intros Hincl a. rewrite ?in_concat. naive_solver. Qed.

Lemma take_incl {A} (l: list A) n:
  incl (take n l) l.
Proof. intros a. rewrite -{2}(firstn_skipn n l) in_app_iff. auto. Qed.

Lemma fmap_incl {A B} (f: A → B) (l l': list A):
  incl l l' →
  incl (fmap f l) (fmap f l').
Proof.
  intros Hincl a. rewrite -?elem_of_list_In.
  intros (?&?&Hin')%elem_of_list_fmap. subst.
  apply elem_of_list_fmap. eexists; split; eauto.
  move: Hin'. rewrite ?elem_of_list_In. eauto.
Qed.

Lemma log_crash_to_wf σ σ' x :
  wal_wf σ →
  relation.denote log_crash σ σ' x →
  wal_wf σ'.
Proof.
  simpl.
  intros Hwf Htrans; monad_inv.
  destruct Hwf as (Haddrs&Hmono&Hb1&hb2).
  split_and!; simpl.
  - rewrite /log_state.updates; simpl.
    eapply incl_Forall; eauto.
    apply concat_mono, fmap_incl, take_incl.
  - move: Hmono.
    rewrite -{1}(firstn_skipn (crash_txn) (σ.(log_state.txns))).
    rewrite fmap_app list_mono_app; naive_solver.
  - lia.
  - len.
Qed.

Lemma is_highest_txn_implies_non_empty_txns γ cs txns installed_txn_id:
  is_highest_txn txns installed_txn_id (start cs) →
  txns ≠ [].
Proof.
  rewrite /is_highest_txn/is_txn.
  rewrite fmap_Some.
  intros ((?&Hlookup&_)&_).
  apply elem_of_list_lookup_2 in Hlookup.
  destruct txns; eauto.
  set_solver.
Qed.

(* XXX: I think this suggests that we're going to have to require the initial state
   to have a non empty list of txns. *)
Lemma is_installed_txn_implies_non_empty_txns γ cs txns installed_txn_id lb:
  is_installed_txn γ cs txns installed_txn_id lb -∗
  ⌜ txns ≠ [] ⌝.
Proof. iNamed 1. iPureIntro; by eapply is_highest_txn_implies_non_empty_txns. Qed.

Lemma circ_matches_txns_crash cs txns installed_txn_id diskEnd_txn_id:
  circ_matches_txns cs txns installed_txn_id diskEnd_txn_id →
  circ_matches_txns cs (take (diskEnd_txn_id) txns) installed_txn_id diskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns/has_updates.
  intros Heq d. rewrite Heq /subslice take_idemp //=.
Qed.

Lemma is_txn_from_take_is_txn n txns id pos:
  is_txn (take n txns) id pos →
  is_txn txns id pos.
Proof.
  rewrite /is_txn.
  rewrite ?fmap_Some.
  intros (x&Hlookup&Hpos).
  eexists; split; eauto.
  rewrite -(firstn_skipn n txns).
  apply lookup_app_l_Some; eauto.
Qed.

Lemma is_wal_inner_durable_post_crash l γ σ cs P':
  (∀ σ', relation.denote (log_crash) σ σ' tt → IntoCrash (P σ) (P' σ')) →
  "Hinner" ∷ is_wal_inner l γ σ ∗ "HP" ∷ P σ ∗
  "Hcirc" ∷ is_circular_state γ.(circ_name) cs ∗ "γcs" ∷ circular_pred γ cs  -∗
  post_crash (λ hG, ∃ σ', ⌜ relation.denote (log_crash) σ σ' tt ⌝ ∗
                            is_wal_inner_durable γ σ' ∗
                            P' σ' hG).
Proof.
  rewrite /circular_pred.
  iIntros (Hcrash). iNamed 1.
  rewrite /is_wal_inner_durable.
  iNamed "Hinner".
  iNamed "Hdisk".
  iNamed "Hdisk".

  iPersist "Hdurable".
  unify_ghost.
  clear cs; rename cs0 into cs.
  iDestruct (is_installed_weaken_read with "Hinstalled") as "[Hinstalled _]".
  set (σ':= log_crash_to σ diskEnd_txn_id).
  iDestruct (crash_to_diskEnd with "circ.end Hdurable") as %Htrans.
  specialize (Hcrash _ Htrans).
  iDestruct "circ.start" as %Hcirc_start.
  iDestruct "circ.end" as %Hcirc_end.
  iDestruct "Hdurable" as %Hdurable.
  iCrash.
  iExists _; iFrame "% ∗".
  iSplit.
  { iPureIntro.
    eapply log_crash_to_wf; eauto. }
  iExists cs; iFrame.
  rewrite /disk_inv_durable.
  iExists installed_txn_id, diskEnd_txn_id; simpl.
  assert (installed_txn_id < diskEnd_txn_id).
  { admit. (* TODO: is_installed_read needs an upper bound of diskEnd_txn_id for this to be true *) }
  iSplitL "Hinstalled".
  { admit. (* TODO: is_installed_read needs an upper bound of diskEnd_txn_id for this to be true *) }
  iPureIntro. split_and!.
  - apply circ_matches_txns_crash; auto.
  - naive_solver.
  - destruct Hcirc_start as (Hcirc_start1&Hcirc_start2).
    split; auto.
    * destruct Hcirc_start2 as (Htxn&?). rewrite /is_txn.
      rewrite -Htxn. f_equal.
      (* XXX: this requires installed_txn_id be *strictly* less than diskEnd_txn_id *)
      rewrite lookup_take; eauto. lia.
    * intros.
      destruct Hcirc_start2 as (Htxn&Hhigh). eapply Hhigh.
      eapply is_txn_from_take_is_txn; eauto.
  - destruct Hcirc_end as (x&?&?&?).
    exists x; split_and!; eauto.
    rewrite /is_highest_txn.
    split.
    * rewrite /is_txn.
    (* XXX: This doesn't seem provable, if we have lost diskEnd_txn_id (as we will under
       the current crash to definition). *)
    admit.
Admitted.

Lemma is_wal_post_crash γ P' l:
  (∀ σ σ', relation.denote (log_crash) σ σ' tt →
           IntoCrash (P σ) (P' σ')) →
  is_wal P l γ ={↑walN, ∅}=∗ ▷
  post_crash (λ hG, ∃ σ σ', ⌜ relation.denote (log_crash) σ σ' tt ⌝ ∗ is_wal_inner_durable γ σ' ∗ P' σ' hG).
Proof.
Abort.

(* holds for log states which are possible after a crash (essentially these have
no mutable state) *)
Definition wal_post_crash σ: Prop :=
  σ.(log_state.durable_lb) = length σ.(log_state.txns).

Theorem wpc_mkLog_recover k E2 d γ σ :
  {{{ is_wal_inner_durable γ σ }}}
    mkLog #d @ NotStuck; k; ⊤; E2
  {{{ γ' l, RET #l;
       is_wal_inv_pre l γ' σ ∗
       (* XXX whatever it is that background threads needs *)
       True}}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "Hcs HΦ".
  rewrite /mkLog.

  Ltac show_crash1 := eauto.

  wpc_pures; first by show_crash1.
  iNamed "Hcs".
  iNamed "Hdisk".
  wpc_bind (recoverCircular _).

  Ltac show_crash2 :=
    try (crash_case); iExists _;
    iSplitL ""; first auto;
    iFrame; iExists _; iFrame; iExists _, _; iFrame "∗ #".

  wpc_apply (wpc_recoverCircular with "[$]").
  iSplit.
  { iIntros "Hcirc". show_crash2. }


  iNext. iIntros (γcirc' c diskStart diskEnd bufSlice upds).
  iIntros "(Hupd_slice&Hcirc&Happender&Hstart&Hdisk&%&%&%)".

  iDestruct (is_circular_state_wf with "Hcirc") as %Hwf_circ.
  iMod (diskEnd_is_get_at_least with "[$]") as "(Hdisk&#Hdisk_atLeast)".
  iMod (thread_own_alloc with "Hdisk") as (γdiskEnd_avail_name) "(HdiskEnd_exactly&Hthread_end)".
  iMod (start_is_get_at_least with "[$]") as "(Hstart&#Hstart_atLeast)".
  iMod (thread_own_alloc with "Hstart") as (γstart_avail_name) "(Hstart_exactly&Hthread_start)".
  iMod (ghost_var_alloc σ.(log_state.txns)) as (γtxns_name) "(γtxns & Howntxns)".
  (* TODO: allocate txns with alloc_txns_ctx *)
  set (γ' := (set circ_name (λ _, γcirc') γ)).

  wpc_frame_compl "Hupd_slice HdiskEnd_exactly Hstart_exactly".
  { crash_case. iExists γ'.
    rewrite /is_wal_inner_durable. simpl. rewrite /is_durable_txn/is_installed_txn/is_durable//=.
    simpl. iSplitL ""; first auto. rewrite /txns_ctx.
    iFrame. iExists _; iFrame.
  }
  wp_pures.
  wp_apply (wp_new_free_lock); iIntros (γlock ml) "Hlock".

  clear γ'.
  set (γ' :=
         (set lock_name (λ _, γlock)
              (set start_avail_name (λ _, γstart_avail_name)
                   (set diskEnd_avail_name (λ _, γdiskEnd_avail_name)
                        (set circ_name (λ _, γcirc') γ))))).
  wp_pures.
  iDestruct (updates_slice_cap_acc with "Hupd_slice") as "[Hupd_slice Hupds_cap]".
  wp_apply (wp_mkSliding with "[$]").
  { destruct Hwf_circ as (?&?). subst; lia. }
  iIntros (lslide) "Hsliding".
  iDestruct (is_sliding_wf with "[$]") as %Hsliding_wf.
  wp_apply wp_allocStruct; first by auto.
  iIntros (st) "Hwal_state".
  wp_pures.
  iMod (alloc_lock _ _ _ _ (wal_linv st γ') with "[$] [-]").
  { rewrite /wal_linv.
    assert (int.val diskStart + length upds = int.val diskEnd) as Heq_plus.
    { etransitivity; last eassumption. rewrite /circΣ.diskEnd //=. subst. word. }
    iExists {| diskEnd := diskEnd; memLog := _ |}. iSplitL "Hwal_state Hsliding".
    { iExists {| memLogPtr := _; shutdown := _; nthread := _ |}.
      iDestruct (struct_fields_split with "Hwal_state") as "Hwal_state".
      iDestruct "Hwal_state" as "(?&?&?&?&_)".
      iFrame. iPureIntro. rewrite /locked_wf//=.
      { destruct Hwf_circ as (?&?). subst. split.
        * split; first lia. rewrite Heq_plus. word.
        * eauto.
      }
    }
    rewrite //= /diskEnd_linv/diskStart_linv -Heq_plus.
    iFrame. iFrame "Hdisk_atLeast Hstart_atLeast".
    rewrite /memLog_linv //=.
    admit.
  }

Abort.

Theorem wpc_MkLog_recover stk k E1 E2 d γ σ :
  {{{ is_wal_inner_durable γ σ }}}
    MkLog #d @ stk; k; E1; E2
  {{{ σ' γ' l, RET #l;
      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗
       is_wal_inv_pre l γ' σ' }}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ }}}.
Proof.
Abort.

End goose_lang.
