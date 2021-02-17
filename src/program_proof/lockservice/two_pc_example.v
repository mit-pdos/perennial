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

Section res_map.

Context `{!heapG Σ}.

Definition oneShotResMapUR Σ (K:Type) `{Countable K}: ucmra :=
  gmapUR K (csumR (fracR) (agreeR (laterO (iPropO Σ)))).

Class resMapG Σ K `{Countable K} :=
  { resMap_inG :> inG Σ (oneShotResMapUR Σ K); }.

Context {K:Type} `{Countable K}.
Context `{!resMapG Σ K}.

Definition res_unshot γ (k:K) q :=
  own γ {[ k := Cinl q ]}.

Definition res_ro γ (k:K) (R:iProp Σ) :=
  own γ {[ k := Cinr (to_agree (Next R)) ]}.

Notation "k r[[ γ ]]↦{ q } ?" := (res_unshot γ k q%Qp)
  (at level 20, q at level 50, format "k r[[ γ ]]↦{ q } ?") : bi_scope.
Notation "k r[[ γ ]]↦ ?" := (k r[[γ]]↦{1} ?)%I
  (at level 20, format "k r[[ γ ]]↦ ?") : bi_scope.
Notation "k r[[ γ ]]↦ P" := (res_ro γ k P)
  (at level 20, format "k  r[[ γ ]]↦ P") : bi_scope.

Lemma rptsto_choose R γ k :
  k r[[γ]]↦? ==∗ k r[[γ]]↦ R.
Proof.
Admitted.

Lemma rptsto_agree γ k P Q:
  k r[[γ]]↦ P -∗ k r[[γ]]↦ Q -∗ ▷(P ≡ Q).
Proof.
  iIntros "HP HQ".
  iCombine "HP HQ" as "HPQ".
  iDestruct (own_valid with "HPQ") as "#Hvalid".
  rewrite -Cinr_op.
  rewrite singleton_validI.
  iAssert (✓ (to_agree (Next P) ⋅ to_agree (Next Q)))%I as "#Hvalid2".
  { admit. }
  iDestruct (wsat.agree_op_invI with "Hvalid2") as "#Hvalid3".
  iEval (rewrite agree_equivI) in "Hvalid3".
  Search Next.
  by iApply later_equivI_1.
Admitted.

(* TODO: put in helper lemmas *)
End res_map.

Notation "k r[[ γ ]]↦{ q } ?" := (res_unshot γ k q)
  (at level 20, q at level 50, format "k r[[ γ ]]↦{ q } ?") : bi_scope.
Notation "k r[[ γ ]]↦?" := (res_unshot γ k 1%Qp)
  (at level 20, format "k r[[ γ ]]↦?") : bi_scope.
Notation "k r[[ γ ]]↦ P" := (res_ro γ k P)
  (at level 20, format "k  r[[ γ ]]↦ P") : bi_scope.

Section tpc_example.

Context `{!heapG Σ}.
Context `{!mapG Σ u64 u64}.
Context `{!mapG Σ u64 ()}.
Context `{!mapG Σ u64 (option bool)}.
Context `{!mapG Σ (u64*u64) ()}.
Context `{resMapG Σ (u64*u64) }.

Record tpc_names :=
mk_tpc_names  {
  committed_gn : gname ; (* tid -> option bool *)
  prepared_gn : gname ;  (* (tid, pid) -> () *)
  finish_token_gn : gname ;
  uncommit_token_gn : gname ;
  abort_res_gn : gname ; (* (tid,pid) -> iProp *)
  commit_res_gn : gname ; (* (tid,pid) -> iProp *)
}.

Implicit Type γtpc : tpc_names.

Definition unprepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ ().
Definition prepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ro ().
Definition finish_token γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(finish_token_gn)]]↦ ().
Definition uncommit_token γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(uncommit_token_gn)]]↦ ().
Definition committed_witness γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(uncommit_token_gn)]]↦ro ().

Definition undecided γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ None.
Definition aborted γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ro Some false.
Definition committed γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ro Some true.

Definition tpc_inv_single γtpc tid pid : iProp Σ :=
  unprepared γtpc tid pid ∗ uncommit_token γtpc tid pid ∗
      ((tid,pid) r[[γtpc.(abort_res_gn)]]↦?) ∗
      ((tid,pid) r[[γtpc.(commit_res_gn)]]↦?) ∨
  prepared γtpc tid pid ∗ uncommit_token γtpc tid pid ∗ (∃ R, R ∗ (tid, pid) r[[γtpc.(abort_res_gn)]]↦ R) ∨
  committed γtpc tid ∗ prepared γtpc tid pid ∗ ((∃ R, R ∗ (tid, pid) r[[γtpc.(commit_res_gn)]]↦ R) ∨ finish_token γtpc tid pid) ∨
  aborted γtpc tid ∗ finish_token γtpc tid pid
.

Definition txnSingleN (pid:u64) := nroot .@ "tpc" .@ pid.
Definition is_txn_single γtpc (tid pid:u64): iProp Σ := inv (txnSingleN pid) (tpc_inv_single γtpc tid pid).

Lemma participant_prepare E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid -∗ finish_token γtpc tid pid -∗ R ={E}=∗
  prepared γtpc tid pid ∗ finish_token γtpc tid pid ∗
  ((tid,pid) r[[γtpc.(abort_res_gn)]]↦ R) ∗
  ((tid,pid) r[[γtpc.(commit_res_gn)]]↦ R').
Proof.
  intros ?.
  iIntros "His_txn Hfinish_tok HR".
  iInv "His_txn" as "[>[Hunprep Huncommit]|[[>#Hprep Hrest]|[Hcommitted|Haborted]]]" "Htclose".
  {
    (* TODO: don't use auth_map; want just mapUR *)
    iMod (map_freeze with "[] Hunprep") as "[_ #Hprep]".
    { admit. }

    iFrame "Hprep Hfinish_tok".
    iDestruct "Huncommit" as "(Huncommit & Habort & Hcommit)".
    iMod (rptsto_choose R' with "Hcommit") as "#Hcommit".
    iMod (rptsto_choose R with "Habort") as "#Habort".
    iFrame "#".
    iMod ("Htclose" with "[HR Huncommit]"); last done.
    iNext.
    iRight.
    iLeft.
    iFrame "#∗".
    iExists _; iFrame "#∗".
  }
  { (* Already prepared *)
    iFrame "Hfinish_tok".
    iMod ("Htclose" with "[HR Hrest]"); last done.
    iRight. iLeft. iFrame "#∗".
  }
  { (* Committed *)
    iDestruct "Hcommitted" as "(>Hcom & >#Hprep & Hescrow)".
    iFrame "#∗".
    iMod ("Htclose" with "[Hcom $Hprep Hescrow]"); last done.
    iNext.
    iRight.
    iRight.
    iLeft.
    iFrame.
  }
  { (* Aborted *)
    iDestruct "Haborted" as "[_ >Hfinish_tok2]".
    iDestruct (ptsto_valid_2 with "Hfinish_tok2 Hfinish_tok") as %Hval.
    contradiction.
  }
Admitted.

Lemma prepared_participant_abort E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ prepared γtpc tid pid -∗ aborted γtpc tid -∗ finish_token γtpc tid pid ={E}=∗
  ▷ R.
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hprep #Habort Hfinish_tok".

  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>[Hunprep _]|Ht]".
  { (* Unprepared *)
    iDestruct (ptsto_agree_frac_value with "Hprep Hunprep") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & $ &_)|Ht]".
  { (* Prepared *)
    iMod ("Htclose" with "[Hfinish_tok $Habort]"); eauto.
  }
  iDestruct "Ht" as "[[>#Hcom _]|Ht]".
  {
    iDestruct (ptsto_agree_frac_value with "Hcom Habort") as %[Hbad _].
    naive_solver.
  }
  iDestruct "Ht" as "[_ >Hfinish_tok2]".
  {
    iDestruct (ptsto_conflict with "Hfinish_tok Hfinish_tok2") as %Hbad.
    contradiction.
  }
Qed.

(* Need to know that committed implies prepared *)
Lemma prepared_participant_finish_commit E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ committed_witness γtpc tid pid -∗ committed γtpc tid -∗ finish_token γtpc tid pid ={E}=∗
  ▷ R'.
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hcommit_tok #Hcom Hfinish_tok".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>[_ Huncommit]|Ht]".
  { (* Unprepared *)
    iDestruct (ptsto_agree_frac_value with "Huncommit Hcommit_tok") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & _ & >Huncommit)|Ht]".
  { (* Prepared *)
    iDestruct (ptsto_agree_frac_value with "Huncommit Hcommit_tok") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & #Hprep & HR')|Ht]".
  {
    iDestruct "HR'" as "[$|>Hfinish_tok2]".
    {
      iMod ("Htclose" with "[$Hcom $Hprep Hfinish_tok]"); last by iModIntro.
      iNext. eauto.
    }
    {
      iDestruct (ptsto_conflict with "Hfinish_tok Hfinish_tok2") as %Hbad.
      contradiction.
    }
  }
  iDestruct "Ht" as "[>#Habort _]".
  { (* aborted *)
    iDestruct (ptsto_agree_frac_value with "Hcom Habort") as %[Hbad _].
    naive_solver.
  }
Qed.

Lemma start_commit_txn_single E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ prepared γtpc tid pid -∗ undecided γtpc tid ={E,E∖↑txnSingleN pid}=∗
  undecided γtpc tid ∗ committed_witness γtpc tid pid ∗ (▷ R) ∗ (R' -∗ committed γtpc tid ={E ∖ ↑txnSingleN pid,E}=∗ emp).
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hprep Hundecided".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>[Hunprep _]|Ht]".
  { (* Unprepared *)
    iDestruct (ptsto_agree_frac_value with "Hprep Hunprep") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & $ & >Huncommit)|Ht]".
  {
    iMod (map_freeze with "[] Huncommit") as "[_ #Hcommit_witness]".
    { admit. }
    iFrame "#∗".
    iModIntro.
    iIntros "HR' #Hcommitted".
    iApply "Htclose".
    iNext.
    iRight. iRight. iLeft.
    iFrame "#∗".
  }
  iDestruct "Ht" as "[[>#Hcom _]|Ht]".
  {
    iDestruct (ptsto_agree_frac_value with "Hundecided Hcom") as %[Hbad _].
    naive_solver.
  }
  iDestruct "Ht" as "[>#Habort _]".
  {
    iDestruct (ptsto_agree_frac_value with "Hundecided Habort") as %[Hbad _].
    naive_solver.
  }
Admitted.

(* Proof of participant code *)
Record participant_names :=
mk_participant_names  {
    ps_ghs:list (deletable_heap.gen_heapG u64 bool Σ) ;
    ps_kvs:gname ;
    ps_kvs_phys:gname ;
    ps_kph:gname
}.

Implicit Type γ : participant_names.

Record TransactionC :=
mkTransactionC {
    heldResource:u64;
    oldValue:u64;
    operation:u64;
    amount:u64
}.

#[refine] Instance TransactionC_IntoVal : into_val.IntoVal (TransactionC) :=
  {
  to_val := λ x, (#x.(heldResource), (
          (#x.(oldValue),
          (#x.(operation),
          (#x.(amount), #())))))%V ;
  IntoVal_def := mkTransactionC 0 0 0 0 ;
  IntoVal_inj := _
  }.
Proof.
  intros x1 x2 [=].
  destruct x1. destruct x2.
  simpl in *. subst.
  done.
Defined.

Instance unit_IntoVal : into_val.IntoVal ().
Proof.
  refine {| into_val.to_val := λ _, #();
            into_val.IntoVal_def := ();
         |}.
  intros [] [] _; auto.
Defined.

Definition kv_ctx γ (kvsM:gmap u64 u64) k : iProp Σ :=
  k [[γ.(ps_kvs)]]↦{3/4} (map_get kvsM k).1 ∗ k [[γ.(ps_kvs_phys)]]↦ (map_get kvsM k).1 ∨ k [[γ.(ps_kph)]]↦ () ∗ k [[γ.(ps_kvs_phys)]]↦{1/2} (map_get kvsM k).1.

Definition ps_mu_inv (ps:loc) γ γtpc pid : iProp Σ :=
  ∃ (kvs_ptr txns_ptr finishedTxns_ptr lockMap_ptr:loc) (kvsM:gmap u64 u64) (txnsM:gmap u64 TransactionC)
    (finishedTxnsM:gmap u64 bool),

    "Hkvs" ∷ ps ↦[ParticipantServer.S :: "kvs"] #kvs_ptr ∗
    "Htxns" ∷ ps ↦[ParticipantServer.S :: "txns"] #txns_ptr ∗
    "HfinishedTxns" ∷ ps ↦[ParticipantServer.S :: "finishedTxns"] #finishedTxns_ptr ∗

    "HlockMap_ptr" ∷ ps ↦[ParticipantServer.S :: "lockmap"] #lockMap_ptr ∗
    "HkvsMap" ∷ is_map (kvs_ptr) kvsM ∗
    "HtxnsMap" ∷ is_map (txns_ptr) txnsM ∗
    "HfinishedTxnsMap" ∷ is_map (finishedTxns_ptr) finishedTxnsM ∗

    "Hkvs_ctx" ∷ ([∗ set] k ∈ (fin_to_set u64), kv_ctx γ kvsM k) ∗
    "#HlockMap" ∷ is_lockMap lockMap_ptr γ.(ps_ghs) (fin_to_set u64) (λ k, k [[γ.(ps_kph)]]↦ ()) ∗

    "#Htxnx_prepared" ∷ ([∗ map] tid ↦ txn ∈ txnsM, (prepared γtpc tid pid)) ∗
    "Hfinish_tok" ∷ ([∗ set] tid ∈ (fin_to_set u64), (⌜is_Some (finishedTxnsM !! tid)⌝ ∨ finish_token γtpc tid pid)) ∗
    "%" ∷ ⌜(dom (gset u64) txnsM) ## dom (gset u64) finishedTxnsM⌝
.

Definition participantN := nroot .@ "participant".

Definition is_participant (ps:loc) γ γtpc pid : iProp Σ :=
  ∃ (mu:loc),
  "#Hmu" ∷ readonly (ps ↦[ParticipantServer.S :: "mu"] #mu) ∗
  "#Hmu_inv" ∷ is_lock participantN #mu (ps_mu_inv ps γ γtpc pid)
.

Lemma wp_Participant__PrepareIncrease (ps:loc) tid pid γ γtpc (key amnt:u64) :
  {{{
       is_txn_single γtpc tid pid (∃ v:u64, key [[γ.(ps_kvs)]]↦{3/4} v ∗ key [[γ.(ps_kvs_phys)]]↦{1/2} (word.add v amnt)) (∃ v:u64, key [[γ.(ps_kvs)]]↦{3/4} v ∗ key [[γ.(ps_kvs_phys)]]↦{1/2} v) ∗
       is_participant ps γ γtpc pid
  }}}
    ParticipantServer__PrepareIncrease #ps #tid #key #amnt
  {{{
       (a:u64), RET #a; ⌜a ≠ 0⌝ ∨ ⌜a = 0⌝ ∗ prepared γtpc tid pid
  }}}.
Proof.
  iIntros (Φ) "[#Htxn #Hps] HΦ".
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
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfinish_tok]").
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
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfinish_tok]").
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
  wp_apply (wp_MapInsert _ _ _ _ (mkTransactionC _ _ _ _) with "HtxnsMap").
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
  iDestruct "Hptsto" as "[Hptsto|[Hbad _]]"; last first.
  { iDestruct (ptsto_conflict with "Hbad Hkph") as %Hbad. contradiction. }
  iDestruct "Hptsto" as "[Hlogptsto Hphysptsto]".
  iMod (map_update _ _ (word.add old_v4 amnt) with "[] Hphysptsto") as "[_ Hphysptsto]".
  { admit. }
  iDestruct "Hphysptsto" as "[Hphysptsto Hphysptsto2]".
  iSpecialize ("Hkvs_ctx" $! (kv_ctx γ (map_insert kvsM key (word.add old_v4 amnt)))%I with "[] [Hphysptsto2 Hkph]").
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
    unfold map_insert.
    unfold map_get.
    rewrite lookup_insert /=.
    iFrame.
  }
  iDestruct (big_sepS_elem_of_acc _ _ tid with "Hfinish_tok") as "[Hfinish_tok Hfinish_rest]".
  { set_solver. }
  iDestruct "Hfinish_tok" as "[%Hbad|Hfinish_tok]".
  { exfalso. admit. (* use Hmapget_finished and Hbad *) }
  iMod (participant_prepare with "Htxn Hfinish_tok [Hlogptsto Hphysptsto]") as "[#Hprep Hfinish_tok]".
  { done. }
  { iExists _; iFrame.
    rewrite Hmapget_oldv4 /=.
    iFrame.
  }
  iSpecialize ("Hfinish_rest" with "[Hfinish_tok]").
  { by iRight. }

  wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfinish_rest]").
  {
    iNext. iExists _, _, _,_,_,_,_; iFrame "HkvsMap #∗".
    iSplitL.
    {
      iApply big_sepM_insert.
      { apply map_get_false in Hmapget. naive_solver. }
      iFrame "#".
    }
    iPureIntro.
    rewrite dom_insert.
    Search "not_elem_of_dom".
    apply map_get_false in Hmapget_finished.
    assert (tid ∉ dom (gset u64) finishedTxnsM).
    { apply not_elem_of_dom. naive_solver. }
    set_solver.
  }
  wp_pures.
  iApply "HΦ".
  iFrame "Hprep".
  by iRight.
Admitted.

Lemma wp_Participant__Commit (ps:loc) tid pid γ γtpc key amnt:
  {{{
       is_txn_single γtpc tid pid (∃ v:u64, key [[γ.(ps_kvs)]]↦{3/4} v ∗ key [[γ.(ps_kvs_phys)]]↦{1/2} (word.add v amnt)) (∃ v:u64, key [[γ.(ps_kvs)]]↦{3/4} v ∗ key [[γ.(ps_kvs_phys)]]↦{1/2} v) ∗
       is_participant ps γ γtpc pid ∗
       committed_witness γtpc tid pid ∗
       committed γtpc tid
  }}}
    ParticipantServer__Commit #ps #tid
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros (Φ) "(#His_txn & #His_part & #Hcomwit & #Hcom) HΦ".
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
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfinish_tok]").
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
  iMod (prepared_participant_finish_commit with "His_txn Hcomwit Hcom Hfinish_tok") as ">Hptstos".
  { done. }
  iDestruct "Hptstos" as (v) "[Hlogptsto Hphysptsto]".

  iDestruct (big_sepS_elem_of_acc _ _ key with "Hkvs_ctx") as "[Hkv Hkvs_rest]".
  { set_solver. }
  unfold kv_ctx.
  iDestruct "Hkv" as "[[Hbad _]|Hkv]".
  {
    iDestruct (ptsto_mut_agree_frac_value with "Hbad Hlogptsto") as %[_ Hbad].
    exfalso.
    contradiction.
  }
  iDestruct "Hkv" as "[Hkph Hphys2]".
  iDestruct (ptsto_agree with "Hphys2 Hphysptsto") as %->.
  iCombine "Hphys2 Hphysptsto" as "Hphysptsto".
  iSpecialize ("Hkvs_rest" with "[Hphysptsto Hlogptsto]").
  {
    iLeft. iFrame.
  }

  wp_apply (wp_LockMap__Release with "[$HlockMap Hkph]").
  {
    (* TODO: need to know that the key the participant remembered correctly which key it was holding for this transaction *)
    iFrame.
    admit.
  }
Admitted.

End tpc_example.
