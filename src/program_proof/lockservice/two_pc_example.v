From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof Require Import lockmap_proof.

From iris.algebra Require Import excl agree auth gmap csum.

From Perennial.Helpers Require Import Map gset ipm.

From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl agree auth gmap csum.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Import own.
From iris_string_ident Require Import ltac2_string_ident.

Section tpc_example.

(* Protocol:
   Exclusive: Unprepared, DoPrepare, Undecided, Finished
   Idempotents: Prepared, Committed, Aborted

   Prepared ⋅ Uncomitted = Uncomitted    <--- Glue
   Unprepared ⋅ Undecided = Invalid    <--- Glue (implied by above)
   Committed ⋅ Undecided = Invalid
   Committed ⋅ DoDecide = Invalid      <---- this is where we would have glued if tokens were separate from state
   Aborted ⋅ DoDecide = Invalid

   Unprepared ∗ DoPrepare ==∗ Uncomitted (== Prepared ∗ Uncommitted)
   Uncommitted ∗ DoDecide ==∗ Committed
   DoDecide ==∗ Aborted

   Participant owns Finished for any tid ∉ finishedTxns
   Participant owns DoPrepare for any tid ∉ (finishedTxns ∪ txnsM)
   Coordinator owns Unprepared for any fresh tid
   Coordinator owns DoDecide for any fresh tid

   is_participant := inv (Unprepared ∨ Undecided ∗ R ∨ Committed ∗ R' ∨ Aborted ∗ Finished)

   { is_participant }
     Paricipant__Prepare
   { Prepared }

   { is_participant ∗ Committed }
   Participant__Commit
   { emp }
   { is_participant ∗ Aborted }
   Participant__Abort
 *)


Context `{!heapG Σ}.
Definition one_shot_decideR := csumR fracR (agreeR boolO).
Definition one_shotR := csumR fracR (agreeR unitO).
Context `{!inG Σ (gmapUR u64 one_shotR)}.
Context `{!inG Σ (gmapUR u64 one_shot_decideR)}.
Context `{!inG Σ (gmapUR u64 (exclR unitO))}.

Record tpc_names :=
mk_tpc_names  {
  prep_gn: gname ;
  commit_gn: gname ;
  finish_gn : gname ;
}.

Implicit Type γtpc : tpc_names.

Definition prepared γtpc (tid:u64) : iProp Σ := own γtpc.(prep_gn) {[ tid := Cinr (to_agree ()) ]}.

Definition undecided γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinl (1/2)%Qp) ]} ∗ prepared γtpc tid.
Definition do_decide γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinl (1/2)%Qp) ]}.
Definition aborted γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinr (to_agree false)) ]}.
Definition committed γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinr (to_agree true)) ]}.

Definition unprepared γtpc (tid:u64) : iProp Σ := own γtpc.(prep_gn) {[ tid := (Cinl (1/2)%Qp) ]} ∗ undecided γtpc tid.
Definition do_prepare γtpc (tid:u64) : iProp Σ := own γtpc.(prep_gn) {[ tid := (Cinl (1/2)%Qp) ]}.

Definition finish_tok γtpc (tid:u64) : iProp Σ := own γtpc.(finish_gn) {[ tid := (Excl ()) ]}.

Definition tpc_inv_single γtpc tid R R' : iProp Σ :=
  unprepared γtpc tid ∨
  undecided γtpc tid ∗ R ∨
  committed γtpc tid ∗ (R' ∨ finish_tok γtpc tid) ∨
  aborted γtpc tid ∗ (R ∨ finish_tok γtpc tid)
.

Definition txnSingleN (pid:u64) := nroot .@ "tpc" .@ pid.
Definition is_prepared γtpc (tid pid:u64) R R' : iProp Σ := inv (txnSingleN pid) (tpc_inv_single γtpc tid R R').

Lemma participant_prepare E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  undecided_half γtpc tid -∗ R ={E}=∗ is_prepared γtpc tid pid R R'
.
Proof.
  iIntros.
  iMod (inv_alloc with "[-]") as "$"; last by iModIntro.
  iNext. iLeft. iFrame.
Qed.

Lemma commit_abort_false γtpc tid :
  committed γtpc tid -∗ aborted γtpc tid -∗ False.
Proof.
  iIntros "Hcommit Habort".
  iDestruct (own_valid_2 with "Hcommit Habort") as %Hbad.
  exfalso. rewrite singleton_op in Hbad.
  setoid_rewrite singleton_valid in Hbad.
  rewrite -Cinr_op in Hbad.
  setoid_rewrite Cinr_valid in Hbad.
  setoid_rewrite to_agree_op_valid in Hbad.
  done.
Qed.

Lemma undecided_commit_false γtpc tid :
  committed γtpc tid -∗ undecided_half γtpc tid -∗ False.
Proof.
  iIntros "Hcommit Hundecided".
  iDestruct (own_valid_2 with "Hcommit Hundecided") as %Hbad.
  exfalso. rewrite singleton_op in Hbad.
  setoid_rewrite singleton_valid in Hbad.
  contradiction.
Qed.

Lemma undecided_abort_false γtpc tid :
  aborted γtpc tid -∗ undecided_half γtpc tid -∗ False.
Proof.
  iIntros "Habort Hundecided".
  iDestruct (own_valid_2 with "Habort Hundecided") as %Hbad.
  exfalso. rewrite singleton_op in Hbad.
  setoid_rewrite singleton_valid in Hbad.
  contradiction.
Qed.

Lemma undecided_commit γtpc tid :
  undecided_half γtpc tid -∗ undecided_half γtpc tid ==∗ committed γtpc tid.
Proof.
  iIntros "Hundec1 Hundec2". iCombine "Hundec1 Hundec2" as "Hundec".
  iMod (own_update _ _ {[ tid := (Cinr (to_agree true)) ]} with "Hundec") as "$".
  {
    apply singleton_update. rewrite -Cinl_op. rewrite frac_op.
    rewrite Qp_half_half. by apply cmra_update_exclusive.
  }
  by iModIntro.
Qed.

Lemma undecided_abort γtpc tid :
  undecided_half γtpc tid -∗ undecided_half γtpc tid ==∗ aborted γtpc tid.
Proof.
  iIntros "Hundec1 Hundec2". iCombine "Hundec1 Hundec2" as "Hundec".
  iMod (own_update _ _ {[ tid := (Cinr (to_agree false)) ]} with "Hundec") as "$".
  {
    apply singleton_update. rewrite -Cinl_op. rewrite frac_op.
    rewrite Qp_half_half. by apply cmra_update_exclusive.
  }
  by iModIntro.
Qed.

Lemma finish_finish_false γtpc tid :
  finish_token γtpc tid -∗ finish_token γtpc tid -∗ False.
Proof.
  iIntros "Hfinish_tok Hfinish_tok2".
  iDestruct (own_valid_2 with "Hfinish_tok Hfinish_tok2") as %Hbad.
  exfalso. rewrite singleton_op in Hbad. setoid_rewrite singleton_valid in Hbad.
  contradiction.
Qed.

Lemma prepared_participant_abort E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_prepared γtpc tid pid R R' -∗
  undecided_half γtpc tid ={E}=∗
  aborted γtpc tid.
Proof.
  intros Hnamespace.
  iIntros "#His_prep Hundec".
  iInv "His_prep" as "Hp" "Hpclose".
  iDestruct "Hp" as "[[>Hundec2 HR]|Hbad]".
  {
    iMod (undecided_abort with "Hundec Hundec2") as "#$".
    iMod ("Hpclose" with "[-]") as "_"; last by iModIntro.
    iRight; iRight.
    iFrame "#∗".
  }
  iDestruct "Hbad" as "[[>#Hbad _]|[>#Hbad _]]".
  {
    iExFalso. iApply undecided_commit_false; eauto.
  }
  {
    iExFalso. iApply undecided_abort_false; eauto.
  }
Qed.

Lemma prepared_participant_finish_commit E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_prepared γtpc tid pid R R' -∗ committed γtpc tid -∗ finish_token γtpc tid ={E}=∗
  ▷ R'.
Proof.
  intros Hnamespace.
  iIntros "#His_prep #Hcommit Hfinish_tok".
  iInv "His_prep" as "Hp" "Hpclose".
  iDestruct "Hp" as "[[>Huncommit _]|Hp]".
  { (* Undecided *)
    iExFalso. iApply undecided_commit_false; eauto.
  }
  iDestruct "Hp" as "[[_ HRfinish]|Hp]".
  {
    iDestruct "HRfinish" as "[HR | >HRfinish]"; last first.
    { iExFalso. iApply (finish_finish_false with "Hfinish_tok HRfinish"). }
    iFrame "HR".
    iMod ("Hpclose" with  "[Hfinish_tok]"); last by iModIntro.
    iRight; iLeft; iFrame "#∗".
  }
  iDestruct "Hp" as "[>Habort _]".
  { (* aborted *)
    iExFalso. iApply commit_abort_false; eauto.
  }
Qed.

Lemma prepared_participant_start_commit E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_prepared γtpc tid pid R R' -∗ undecided_half γtpc tid ={E,E∖↑txnSingleN pid}=∗
  committed γtpc tid ∗ ▷ R ∗ (▷ R' ={E ∖ ↑txnSingleN pid,E}=∗ emp).
Proof.
  intros Hnamespace.
  iIntros "#His_prep Hundec".
  iInv "His_prep" as "Hp" "Hpclose".
  iDestruct "Hp" as "[[>Hundec2 $]|Hp]".
  {
    iMod (undecided_commit with "Hundec Hundec2") as "#$".
    iIntros "!> HR'".
    iApply "Hpclose".
    iNext. iRight. iLeft. iFrame "#". iLeft. iFrame.
  }
  iDestruct "Hp" as "[[#>Hcommitted _]|Hp]".
  {
    iExFalso. iApply undecided_commit_false; eauto.
  }
  iDestruct "Hp" as "[>#Habort _]".
  { iExFalso. iApply undecided_abort_false; eauto. }
Qed.

(* Proof of participant code *)
Record participant_names :=
mk_participant_names  {
    ps_tpc:tpc_names ;
    ps_ghs:list (deletable_heap.gen_heapG u64 bool Σ) ;
    ps_kvs:gname ;
}.

Implicit Type γ : participant_names.

Instance unit_IntoVal : into_val.IntoVal ().
Proof.
  refine {| into_val.to_val := λ _, #();
            into_val.IntoVal_def := ();
         |}.
  intros [] [] _; auto.
Defined.

Context `{!mapG Σ u64 u64}.

Record TxnResourcesC :=
mkTxnResourcesC {
    key:u64;
    oldValue:u64;
}.

Global Instance TransactionC_Inhabited : Inhabited TxnResourcesC :=
  {| inhabitant := mkTxnResourcesC 0 0 |}.

#[refine] Instance TransactionC_IntoVal : into_val.IntoVal (TxnResourcesC) :=
  {
  to_val := λ x, (#x.(key), (
          (#x.(oldValue), #()))) %V ;
  IntoVal_def := mkTxnResourcesC 0 0 ;
  IntoVal_inj := _
  }.
Proof.
  intros x1 x2 [=].
  destruct x1. destruct x2.
  simpl in *. subst.
  done.
Defined.


Definition kv_ctx γ (kvsM:gmap u64 u64) k : iProp Σ :=
  k [[γ.(ps_kvs)]]↦{3/4} (map_get kvsM k).1 ∨
  (Locked γ.(ps_ghs) k).

Definition ps_mu_inv (ps:loc) γ pid : iProp Σ :=
  ∃ (kvs_ptr txns_ptr finishedTxns_ptr lockMap_ptr:loc) (kvsM:gmap u64 u64) (txnsM:gmap u64 TxnResourcesC)
    (finishedTxnsM:gmap u64 bool),

    "Hkvs" ∷ ps ↦[ParticipantServer.S :: "kvs"] #kvs_ptr ∗
    "Htxns" ∷ ps ↦[ParticipantServer.S :: "txns"] #txns_ptr ∗
    "HfinishedTxns" ∷ ps ↦[ParticipantServer.S :: "finishedTxns"] #finishedTxns_ptr ∗

    "HlockMap_ptr" ∷ ps ↦[ParticipantServer.S :: "lockmap"] #lockMap_ptr ∗
    "HkvsMap" ∷ is_map (kvs_ptr) kvsM ∗
    "HtxnsMap" ∷ is_map (txns_ptr) txnsM ∗
    "HfinishedTxnsMap" ∷ is_map (finishedTxns_ptr) finishedTxnsM ∗

    "Hkvs_ctx" ∷ ([∗ set] k ∈ (fin_to_set u64), kv_ctx γ kvsM k) ∗
    "#HlockMap" ∷ is_lockMap lockMap_ptr γ.(ps_ghs) (fin_to_set u64) (λ _, True) ∗

    "#Htxns_prop_pers" ∷ ([∗ map] tid ↦ txn ∈ txnsM, is_prepared γ.(ps_tpc) tid pid (txn.(key) [[γ.(ps_kvs)]]↦{3/4} txn.(oldValue)) (txn.(key) [[γ.(ps_kvs)]]↦{3/4} (map_get kvsM txn.(key)).1) ) ∗
    "Hundec_tok" ∷ ([∗ set] tid ∈ (fin_to_set u64), (⌜tid ∈ dom (gset u64) finishedTxnsM⌝ ∨ ⌜tid ∈ dom (gset u64) txnsM⌝ ∨ undecided_half γ.(ps_tpc) tid)) ∗
    "Hfinish_tok" ∷ ([∗ set] tid ∈ (fin_to_set u64), (⌜tid ∈ dom (gset u64) finishedTxnsM⌝ ∨ finish_token γ.(ps_tpc) tid)) ∗
    "%" ∷ ⌜(dom (gset u64) txnsM) ## dom (gset u64) finishedTxnsM⌝
.

Definition participantN := nroot .@ "participant".

Definition is_participant (ps:loc) γ pid : iProp Σ :=
  ∃ (mu:loc),
  "#Hmu" ∷ readonly (ps ↦[ParticipantServer.S :: "mu"] #mu) ∗
  "#Hmu_inv" ∷ is_lock participantN #mu (ps_mu_inv ps γ pid)
.

Lemma wp_Participant__PrepareIncrease (ps:loc) tid pid γ (key amnt:u64) :
  {{{
       is_participant ps γ pid
  }}}
    ParticipantServer__PrepareIncrease #ps #tid #key #amnt
  {{{
       (a oldv:u64), RET #a; ⌜a ≠ 0⌝ ∨ ⌜a = 0⌝ ∗
       is_prepared γ.(ps_tpc) tid pid (key [[γ.(ps_kvs)]]↦{3/4} oldv) (key [[γ.(ps_kvs)]]↦{3/4} (word.add oldv amnt))
  }}}.
Proof.
  iIntros (Φ) "#Hps HΦ".
  iNamed "Hps".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hmulocked Hps]".
  iNamed "Hps".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HtxnsMap").
  iIntros (txn ok) "[%Hmapget HtxnsMap]".
  wp_pures.
  wp_if_destruct.
  {
    (* Use Htxns_prepared *)
    admit.
  }
  wp_loadField.
  wp_apply (wp_MapGet with "HfinishedTxnsMap").
  iIntros (vfinished okFinished) "[%Hmapget_finished HfinishedTxnsMap]".
  wp_pures.
  wp_if_destruct.
  { (* Transaction already finished *)
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hundec_tok Hfinish_tok]").
    {
      iNext. iExists _, _, _,_,_,_,_; iFrame "#∗".
      done.
    }
    wp_pures.
    iApply "HΦ".
    by iLeft.
  }
  (* Transaction ID has not finished, or been prepared *)
  wp_loadField.
  wp_apply (wp_LockMap__Acquire with "[$HlockMap]").
  { iPureIntro. set_solver. }
  iIntros "[Hkph Hkeylocked]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v old_v_ok) "[%Hmapget_v HkvsMap]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v' ok') "[%Hmapgetold_v HkvsMap]".
  wp_pures.
  wp_if_destruct.
  {
    (* Unsafe increase *)
    wp_loadField. wp_apply (wp_LockMap__Release with "[$HlockMap $Hkeylocked $Hkph]").
    wp_pures.
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hundec_tok Hfinish_tok]").
    {
      iNext. iExists _, _, _,_,_,_,_; iFrame "#∗".
      done.
    }
    wp_pures.
    iApply "HΦ".
    by iLeft.
  }

  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v3 ok_old_v3) "[%Hmapget_v3 HkvsMap]".
  wp_loadField.
  wp_apply (wp_MapInsert _ _ _ _ (mkTxnResourcesC _ _) with "HtxnsMap").
  { eauto. }
  iIntros "HtxnsMap".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v4 ok4) "[%Hmapget_oldv4 HkvsMap]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "HkvsMap").
  { eauto. }
  iIntros "HkvsMap".
  wp_pures.

  iDestruct (big_sepS_elem_of_acc_impl key with "Hkvs_ctx") as "[Hptsto Hkvs_ctx]".
  { set_solver. }
  iDestruct "Hptsto" as "[Hptsto|Hbad]"; last first.
  { admit. (* conflict Hbad Hkeylocked *) }
  iSpecialize ("Hkvs_ctx" $! (λ k, kv_ctx γ (typed_map.map_insert kvsM key (word.add old_v4 amnt)) k)%I with "[] [Hkeylocked]").
  { iModIntro. iIntros.
    unfold kv_ctx.
    rewrite map_get_val.
    rewrite map_get_val.
    unfold map_insert.
    rewrite lookup_insert_ne; last by done.
    iFrame.
  }
  {
    unfold kv_ctx.
    iRight.
    iFrame.
  }

  (* Get unused undecided_half token *)
  iDestruct (big_sepS_elem_of_acc_impl tid with "Hundec_tok") as "[Hundec Hundec_rest]".
  { set_solver. }
  iDestruct "Hundec" as "[%Hbad|[%Hbad|Hundec]]".
  { exfalso. apply map_get_false in Hmapget_finished as [Hbad2 _].
    apply (not_elem_of_dom finishedTxnsM) in Hbad2. set_solver. }
  { exfalso. apply map_get_false in Hmapget as [Hbad2 _].
    apply (not_elem_of_dom txnsM) in Hbad2. set_solver. }
  iMod (participant_prepare with "Hundec Hptsto") as "#His_prep".
  { done. }

  wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hundec_rest Hfinish_tok]").
  {
    iNext. iExists _, _, _,_,_,_,_; iFrame "HkvsMap HtxnsMap #∗".
    iSplitL "".
    { (* Need to have all prepared tokens *)
      iApply big_sepM_insert.
      { apply map_get_false in Hmapget. naive_solver. }
      rewrite Hmapget_v3.
      simpl.
      iFrame "His_prep".
      iApply (big_sepM_impl with "Htxns_prop_pers").
      iModIntro. iIntros.
    }
    iSplitL "Htxns_own Hphysptsto".
    {
      rewrite /typed_map.map_insert.
      iApply (big_sepM_insert_2 with "[Hphysptsto] Htxns_own").
      simpl.
      replace (old_v4) with (old_v3); first iFrame.
      rewrite Hmapget_v3 in Hmapget_oldv4.
      naive_solver.
    }
    iSplitL "Hdata_rest".
    {
      iApply "Hdata_rest".
      {
        iModIntro.
        iIntros (???) "[%Hcase|Hcase]".
        - iLeft. iPureIntro. unfold typed_map.map_insert.
          rewrite dom_insert. set_solver.
        - iRight. iFrame.
      }
      {
        iLeft. iPureIntro. unfold typed_map.map_insert.
        rewrite dom_insert. set_solver.
      }
    }

    iPureIntro.
    rewrite dom_insert.
    apply map_get_false in Hmapget_finished.
    assert (tid ∉ dom (gset u64) finishedTxnsM).
    { apply not_elem_of_dom. naive_solver. }
    set_solver.
  }
  wp_pures.
  iApply "HΦ".
  iFrame "Hprep".
  iRight.
  iSplitL ""; first done.
  iFrame "#".
Admitted.

Lemma wp_Participant__Commit (ps:loc) tid pid key oldv op amnt γ γtpc :
  {{{
       is_txn_single γtpc tid pid (λ data, key [[γ.(ps_kvs)]]↦{3/4} data.(oldValue)) (λ data, key [[γ.(ps_kvs)]]↦{3/4} (word.add data.(oldValue) amnt)) ∗
       is_participant ps γ γtpc pid ∗
       committed_witness γtpc tid pid ∗
       committed γtpc tid ∗
       (tid,pid) [[γtpc.(txn_data_gn)]]↦ro Some (mkTransactionC key oldv op amnt)
  }}}
    ParticipantServer__Commit #ps #tid
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros (Φ) "(#His_txn & #His_part & #Hcomwit & #Hcom & #Hdata_key) HΦ".
  wp_lam.
  wp_pures.
  iNamed "His_part".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hmulocked Hps]".
  iNamed "Hps".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HtxnsMap").
  iIntros (txn1 ok1) "[%Hmapget_txn HtxnsMap]".
  wp_pures.
  wp_if_destruct.
  { (* No pending transaction with that TID *)
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfinish_tok Hdata_unused Htxns_own]").
    {
      iNext. iExists _, _, _,_,_,_,_; iFrame "#∗".
      done.
    }
    wp_pures.
    by iApply "HΦ".
  }
  (* Found a transaction with that ID *)
  wp_loadField.
  iDestruct (big_sepS_elem_of_acc_impl tid with "Hfinish_tok") as "[Hfinish_tok Hfinish_rest]".
  { set_solver. }
  iDestruct "Hfinish_tok" as "[%Hbad|Hfinish_tok]".
  {
    exfalso. apply map_get_true in Hmapget_txn.
    apply elem_of_dom in Hbad.
    assert (is_Some (txnsM !! tid)) by eauto.
    apply elem_of_dom in H0.
    set_solver.
  }
  iDestruct (big_sepM_lookup_acc _ _ tid with "Htxns_prop_pers") as "[[_ Hdata] _]".
  { apply map_get_true in Hmapget_txn. done. }
  iDestruct (big_sepM_delete _ _ tid with "Htxns_own") as "[Hphysptsto2 Htxns_own]".
  { apply map_get_true in Hmapget_txn. done. }
  iMod (prepared_participant_finish_commit with "His_txn Hcomwit Hcom Hdata Hfinish_tok") as ">Hptsto".
  { done. }

  iDestruct (big_sepS_elem_of_acc _ _ txn1.(heldResource) with "Hkvs_ctx") as "[Hkv Hkvs_rest]".
  { set_solver. }
  unfold kv_ctx.
  (* Match txn_data held by participant with txn_data passed in by coordinator *)
  iDestruct (ptsto_agree_frac_value with "Hdata Hdata_key") as %[HR _].
  assert (txn1 = mkTransactionC key _ _ _) as -> by naive_solver. simpl.
  iDestruct "Hkv" as "[[_ Hbad]|[Hkvlocked Hphysptsto]]".
  {
    iDestruct (ptsto_mut_agree_frac_value with "Hbad Hptsto") as %[_ Hbad].
    exfalso.
    contradiction.
  }
  iSpecialize ("Hkvs_rest" with "[Hptsto Hphysptsto2 Hphysptsto]").
  {
    iLeft.
    iFrame.
    iDestruct (ptsto_agree_frac_value with "Hphysptsto Hphysptsto2") as %[<- _].
    iCombine "Hphysptsto Hphysptsto2" as "Hphsptsto".
    iFrame.
  }

  wp_apply (wp_LockMap__Release with "[$HlockMap $Hkvlocked]").
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapDelete with "HtxnsMap").
  iIntros "HtxnsMap".
  wp_loadField.
  wp_apply (wp_MapInsert with "HfinishedTxnsMap").
  { done. }
  iIntros "HfinishedTxnsMap".
  wp_pures.
  wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_rest Hfinish_rest Hdata_unused Htxns_own]").
  {
    iNext. iExists _, _, _,_,_,_,_; iFrame "HtxnsMap HfinishedTxnsMap ∗#".
    iSplitL "".
    {
      rewrite /map_del.
      iDestruct (big_sepM_delete _ _ tid with "Htxns_prop_pers") as "[_ $]".
      by apply map_get_true.
    }
    iSplitL "Hfinish_rest".
    {
      iApply "Hfinish_rest".
      {
        iModIntro.
        iIntros (???) "[%Hcase|Hcase]".
        - iLeft. iPureIntro. unfold typed_map.map_insert.
          rewrite lookup_insert_ne; done.
        - iRight. iFrame.
      }
      iLeft. iPureIntro. unfold typed_map.map_insert.
      rewrite lookup_insert. eauto.
    }
    iSplitL "Hdata_unused".
    {
      unfold typed_map.map_insert.
      unfold map_del.
      replace (dom (gset u64) (<[tid:=true]> finishedTxnsM) ∪ dom (gset u64) (delete tid txnsM))
        with (dom (gset u64) finishedTxnsM ∪ dom (gset u64) txnsM).
      { iFrame. }
      replace (dom (gset u64) (<[tid:=true]> finishedTxnsM)) with
      ({[ tid ]} ∪ (dom (gset u64) finishedTxnsM)); last first.
      { admit. }
      (* TODO: annoying gmap domain proof *)
      admit.
    }
    iPureIntro.
    unfold typed_map.map_insert.
    rewrite dom_insert.
    unfold typed_map.map_del.
    rewrite dom_delete.
    set_solver.
  }
  by iApply "HΦ".
Admitted.

Variable s0:loc.
Variable s1:loc.
Variables γ1:participant_names.
Variables γ2:participant_names.

Definition TransactionCoordinator_own (tc:loc) γtpc : iProp Σ :=

  "#His_part1" ∷ is_participant s0 γ1 γtpc 0 ∗
  "#His_part2" ∷ is_participant s1 γ2 γtpc 1 ∗
  "Hs0" ∷ tc ↦[TransactionCoordinator.S :: "s0"] #s0 ∗
  "Hs1" ∷ tc ↦[TransactionCoordinator.S :: "s1"] #s1
.

Lemma wp_Participant__PrepareDecrease (ps:loc) tid pid γ γtpc (key amnt:u64) :
  {{{
       is_txn_single γtpc tid pid (λ data, key [[γ.(ps_kvs)]]↦{3/4} data.(oldValue)) (λ data, key [[γ.(ps_kvs)]]↦{3/4} (word.sub data.(oldValue) data.(amount))) ∗
       is_participant ps γ γtpc pid
  }}}

    ParticipantServer__PrepareDecrease #ps #tid #key #amnt
  {{{
       (a op oldValue:u64), RET #a; ⌜a ≠ 0⌝ ∨ ⌜a = 0⌝ ∗ prepared γtpc tid pid ∗
       (tid,pid) [[γtpc.(txn_data_gn)]]↦ro Some (mkTransactionC key oldValue op amnt)
  }}}.
Proof.
Admitted.

Lemma txn_single_alloc γtpc tid pid R R' :
  (tid, pid) [[γtpc.(prepared_gn)]]↦ () ∗ (tid, pid) [[γtpc.(uncommit_token_gn)]]↦ ()
  ={⊤}=∗
  is_txn_single γtpc tid pid R R'.
Proof.
  (* Just alloc the invariant *)
Admitted.

Lemma wp_TransactionCoordinator__doTransfer {Eo Ei} (tc:loc) γtpc (tid acc1 acc2 amount v1 v2:u64) :
Eo ⊆ ⊤ ∖ ↑txnSingleN 0 ∖ ↑txnSingleN 1 →
  {{{
       TransactionCoordinator_own tc γtpc ∗
       fresh_tid γtpc tid ∗ (* TODO: make this logically-atomic *)

       |={Eo,Ei}=> (acc1 [[γ1.(ps_kvs)]]↦{1/4} v1 ∗ acc2 [[γ2.(ps_kvs)]]↦{1/4} v2) ∗
        ((acc1 [[γ1.(ps_kvs)]]↦{1/4} (word.add v1 amount) ∗ acc2 [[γ2.(ps_kvs)]]↦{1/4} (word.sub v2 amount)) ={Ei,Eo}=∗ emp)
  }}}
    TransactionCoordinator__doTransfer #tc #tid #acc1 #acc2 #amount
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros (? Φ) "(Hown & Hfresh & Hacc_pre) HΦ".
  iNamed "Hown".
  iNamed "Hfresh".

  iDestruct (big_sepS_delete _ _ (U64 0) with "Htokens") as "[Hs0_res Htokens]".
  { set_solver. }
  iDestruct (big_sepS_delete _ _ (U64 1) with "Htokens") as "[Hs1_res Htokens]".
  { set_solver. }
  iMod (txn_single_alloc  with "Hs0_res") as "#Htxn1".
  iMod (txn_single_alloc  with "Hs1_res") as "#Htxn2".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (wp_Participant__PrepareIncrease with "[]").
  { iFrame "His_part1".
    iFrame "Htxn1".
  }
  iIntros (prepared1 ??) "Hprep1".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Participant__PrepareDecrease with "[$His_part2 $Htxn2]").
  iIntros (prepared2 ??) "Hprep2".
  wp_pures.
  wp_apply (wp_and).
  { wp_pures. done. }
  { iIntros. wp_pures. done. }
  wp_if_destruct.
  - (* Both prepared *)
    iDestruct "Hprep1" as "[%Hbad|[_ Hprep1]]".
    { exfalso. naive_solver. }
    iDestruct "Hprep2" as "[%Hbad|[_ Hprep2]]".
    { exfalso. naive_solver. }
    wp_loadField.

    iDestruct "Hprep1" as "[Hprep1 Hdata1]".
    iDestruct "Hprep2" as "[Hprep2 Hdata2]".
    (* Start the commit point *)
    iApply fupd_wp.
    iMod (start_commit_txn_single with "Htxn1 Hprep1 Hundec") as "(Hundec & #Hcom1 & HR1)"; first done.
    iDestruct "HR1" as (txn1) "(>Hptsto1 & Hdata1' & Hclose1)".
    iMod (start_commit_txn_single with "Htxn2 Hprep2 Hundec") as "(Hundec & #Hcom2 & HR2)".
    { admit. } (* namespaces *)
    iDestruct "HR2" as (txn2) "(>Hptsto2 & Hdata2' & Hclose2)".

    (* Match up keys *)
    iDestruct (ptsto_agree_frac_value with "Hdata1 Hdata1'") as %[Hdata1_same _].
    assert (txn1 = mkTransactionC acc1 _ _ _) as -> by naive_solver. simpl.

    iDestruct (ptsto_agree_frac_value with "Hdata2 Hdata2'") as %[Hdata2_same _].
    assert (txn2 = mkTransactionC acc2 _ _ _) as -> by naive_solver. simpl.

    iMod (fupd_mask_subseteq) as "Hmask_close"; last iMod "Hacc_pre".
    { done. }
    iDestruct "Hacc_pre" as "((Hacc1 & Hacc2) & Hacc_close)".
    iDestruct (ptsto_agree_frac_value with "Hptsto1 Hacc1") as %[-> _].
    iDestruct (ptsto_agree_frac_value with "Hptsto2 Hacc2") as %[-> _].
    iCombine "Hptsto1 Hacc1" as "Hacc1".
    iCombine "Hptsto2 Hacc2" as "Hacc2".

    (***************************)
    (* COMMIT POINT *)
    (***************************)
    rewrite Qp_three_quarter_quarter.
    iMod (map_update _ _ (word.add v1 amount) with "[] Hacc1") as "[_ Hacc1]".
    { admit. } (* map_ctx *)
    iMod (map_update _ _ (word.sub v2 amount) with "[] Hacc2") as "[_ Hacc2]".
    { admit. }

    rewrite -Qp_three_quarter_quarter.
    iDestruct (fractional_split_1 with "Hacc1") as "[Hptsto1 Hacc1]".
    iDestruct (fractional_split_1 with "Hacc2") as "[Hptsto2 Hacc2]".

    iMod (map_update _ _ (Some true) with "[] Hundec") as "[_ Hundec]"; first admit.
    iMod (map_freeze with "[] Hundec") as "[_ #Hcom]"; first admit.

    rewrite Qp_three_quarter_quarter.
    iMod ("Hacc_close" with "[$Hacc1 $Hacc2]").
    iMod "Hmask_close".
    iMod ("Hclose2" with "Hptsto2 Hcom") as "_".
    iMod ("Hclose1" with "Hptsto1 Hcom") as "_".

    iModIntro.
    wp_apply (wp_Participant__Commit with "[$His_part1 $Hcom $Hcom1 $Htxn1 $Hdata1]").
    wp_pures.
    wp_loadField.
    wp_apply (wp_Participant__Commit with "[$His_part2 $Hcom Hcom2 Htxn2 Hdata2]").
    {
      admit. (* TODO: commit is only designed for adding, not subtracting *)
    }
    by iApply "HΦ".
  - (* TODO: Abort case *)
    admit.
Admitted.

End tpc_example.
