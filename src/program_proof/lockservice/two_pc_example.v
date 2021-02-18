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
(* Context `{resMapG Σ (u64*u64) }. *)

Record TransactionC :=
mkTransactionC {
    heldResource:u64;
    oldValue:u64;
    operation:u64;
    amount:u64
}.

Global Instance TransactionC_Inhabited : Inhabited TransactionC :=
  {| inhabitant := mkTransactionC 0 0 0 0 |}.

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

Context `{!mapG Σ (u64*u64) (option (TransactionC))}.

Record tpc_names :=
mk_tpc_names  {
  committed_gn : gname ; (* tid -> option bool *)
  prepared_gn : gname ;  (* (tid, pid) -> () *)
  finish_token_gn : gname ;
  uncommit_token_gn : gname ;
  txn_data_gn : gname ; (* (tid,pid) -> (key, oldv) *)
}.

Implicit Type γtpc : tpc_names.

Definition unprepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ ().
Definition prepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ro ().
Definition finish_token γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(finish_token_gn)]]↦ ().
Definition uncommit_token γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(uncommit_token_gn)]]↦ ().
Definition committed_witness γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(uncommit_token_gn)]]↦ro ().

Definition undecided γtpc (tid:u64) : iProp Σ := tid [[γtpc.(committed_gn)]]↦ None.
Definition aborted γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ro Some false.
Definition committed γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ro Some true.

Definition tpc_inv_single γtpc tid pid R R' : iProp Σ :=
  unprepared γtpc tid pid ∗ uncommit_token γtpc tid pid ∨
  prepared γtpc tid pid ∗ uncommit_token γtpc tid pid ∗ (∃ x:TransactionC, (R x) ∗ (tid, pid) [[γtpc.(txn_data_gn)]]↦ro Some x) ∨
  committed γtpc tid ∗ prepared γtpc tid pid ∗ ((∃ x:TransactionC, (R' x) ∗ (tid, pid) [[γtpc.(txn_data_gn)]]↦ro Some x) ∨ finish_token γtpc tid pid) ∨
  aborted γtpc tid ∗ finish_token γtpc tid pid
.

Definition fresh_tid γtpc (tid:u64) : iProp Σ :=
  "Htokens" ∷ ([∗ set] pid ∈ (fin_to_set u64), (tid,pid:u64) [[γtpc.(prepared_gn)]]↦ () ∗
                                    (tid,pid) [[γtpc.(uncommit_token_gn)]]↦ ()) ∗
  "Hundec" ∷ undecided γtpc tid.

Definition txnSingleN (pid:u64) := nroot .@ "tpc" .@ pid.
Definition is_txn_single γtpc (tid pid:u64) R R' : iProp Σ := inv (txnSingleN pid) (tpc_inv_single γtpc tid pid R R').

Lemma participant_prepare x E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ finish_token γtpc tid pid -∗ R x -∗
  ((tid,pid) [[γtpc.(txn_data_gn)]]↦ None) ={E}=∗
  prepared γtpc tid pid ∗ finish_token γtpc tid pid ∗
  ((tid,pid) [[γtpc.(txn_data_gn)]]↦ro Some x).
Proof.
  intros ?.
  iIntros "His_txn Hfinish_tok HR Hdata".
  iInv "His_txn" as "[>[Hunprep Huncommit]|[[>#Hprep Hrest]|[Hcommitted|Haborted]]]" "Htclose".
  {
    (* TODO: don't use auth_map; want just mapUR *)
    iMod (map_freeze with "[] Hunprep") as "[_ #Hprep]".
    { admit. }

    iFrame "Hprep Hfinish_tok".
    iMod (map_update _ _ (Some x) with "[] Hdata") as "[_ Hdata]".
    { admit. }
    iMod (map_freeze with "[] Hdata") as "[_ #Hdata]".
    { admit. }
    Locate viewR.
    iFrame "#".
    iMod ("Htclose" with "[HR Huncommit]"); last done.
    iNext.
    iRight.
    iLeft.
    iFrame "#∗".
    iExists _; iFrame "#∗".
  }
  { (* Already prepared; contradiction *)
    iDestruct "Hrest" as "[_ Hrest]".
    iDestruct "Hrest" as (x2) "[_ >Hdata2]".
    iDestruct (ptsto_agree_frac_value with "Hdata Hdata2") as %[_ Hbad].
    contradiction.
  }
  { (* Committed; contradiction with Hescrow a nd Hfinish_tok ∨ Hdata *)
    iDestruct "Hcommitted" as "(>Hcom & >#Hprep & Hescrow)".
    admit.
  }
  { (* Aborted *)
    iDestruct "Haborted" as "[_ >Hfinish_tok2]".
    iDestruct (ptsto_valid_2 with "Hfinish_tok2 Hfinish_tok") as %Hval.
    contradiction.
  }
Admitted.

Lemma prepared_participant_abort E γtpc tid pid R R' x:
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ prepared γtpc tid pid -∗ (tid,pid) [[γtpc.(txn_data_gn)]]↦ro Some x -∗ aborted γtpc tid -∗ finish_token γtpc tid pid ={E}=∗
  ▷ R x.
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hprep #Hdata #Habort Hfinish_tok".

  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>[Hunprep _]|Ht]".
  { (* Unprepared *)
    iDestruct (ptsto_agree_frac_value with "Hprep Hunprep") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & _ & HR)|Ht]".
  { (* Prepared *)
    iDestruct "HR" as (x') "[HR >Hdata2]".
    iDestruct (ptsto_agree_frac_value with "Hdata Hdata2") as %[H  _].
    replace (x') with (x) by naive_solver.
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
Lemma prepared_participant_finish_commit E γtpc tid pid R R' x:
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ committed_witness γtpc tid pid -∗ committed γtpc tid -∗  (tid,pid) [[γtpc.(txn_data_gn)]]↦ro Some x -∗ finish_token γtpc tid pid ={E}=∗
  ▷ R' x.
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hcommit_tok #Hcom #Hdata Hfinish_tok".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>[_ Huncommit]|Ht]".
  { (* Unprepared *)
    iDestruct (ptsto_agree_frac_value with "Huncommit Hcommit_tok") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & >Huncommit & _)|Ht]".
  { (* Prepared *)
    iDestruct (ptsto_agree_frac_value with "Huncommit Hcommit_tok") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & #Hprep & HR')|Ht]".
  {
    iDestruct "HR'" as "[HR|>Hfinish_tok2]".
    {
      iDestruct "HR" as (x') "[HR' >Hdata2]".
      iDestruct (ptsto_agree_frac_value with "Hdata Hdata2") as %[H  _].
      replace (x') with (x) by naive_solver.
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
  undecided γtpc tid ∗ committed_witness γtpc tid pid ∗ (∃ x, ▷ R x ∗ (tid, pid) [[γtpc.(txn_data_gn)]]↦ro Some x ∗ (R' x -∗ committed γtpc tid ={E ∖ ↑txnSingleN pid,E}=∗ emp)).
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hprep Hundecided".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>[Hunprep _]|Ht]".
  { (* Unprepared *)
    iDestruct (ptsto_agree_frac_value with "Hprep Hunprep") as %[_ Hbad].
    contradiction.
  }
  iDestruct "Ht" as "[(_ & >Huncommit & HR)|Ht]".
  {
    iMod (map_freeze with "[] Huncommit") as "[_ #Hcommit_witness]".
    { admit. }
    iFrame "#∗".
    iDestruct "HR" as (x) "[HR >#Hdata]".
    iExists _; iFrame "#∗".
    iModIntro.
    iIntros "HR' #Hcommitted".
    iApply "Htclose".
    iNext.
    iRight. iRight. iLeft.
    iFrame "#∗".
    iLeft. iExists x.
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
}.

Implicit Type γ : participant_names.

Instance unit_IntoVal : into_val.IntoVal ().
Proof.
  refine {| into_val.to_val := λ _, #();
            into_val.IntoVal_def := ();
         |}.
  intros [] [] _; auto.
Defined.

Definition kv_ctx γ (kvsM:gmap u64 u64) k : iProp Σ :=
  k [[γ.(ps_kvs_phys)]]↦ (map_get kvsM k).1 ∗ k [[γ.(ps_kvs)]]↦{3/4} (map_get kvsM k).1 ∨
  (Locked γ.(ps_ghs) k) ∗ k [[γ.(ps_kvs_phys)]]↦{1/2} (map_get kvsM k).1.

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
    "#HlockMap" ∷ is_lockMap lockMap_ptr γ.(ps_ghs) (fin_to_set u64) (λ _, True) ∗

    "#Htxns_prop_pers" ∷ ([∗ map] tid ↦ txn ∈ txnsM, (prepared γtpc tid pid) ∗ (tid, pid)[[γtpc.(txn_data_gn)]]↦ro Some txn)∗
    "Htxns_own" ∷ ([∗ map] tid ↦ txn ∈ txnsM,  txn.(heldResource) [[γ.(ps_kvs_phys)]]↦{1/2} (word.add txn.(oldValue) txn.(amount))) ∗
    "Hfinish_tok" ∷ ([∗ set] tid ∈ (fin_to_set u64), (⌜is_Some (finishedTxnsM !! tid)⌝ ∨ finish_token γtpc tid pid)) ∗
    "Hdata_unused" ∷ ([∗ set] tid ∈ (fin_to_set u64), (⌜tid ∈ dom (gset u64) finishedTxnsM ∪ dom (gset u64) txnsM⌝ ∨ (tid,pid) [[γtpc.(txn_data_gn)]]↦ None)) ∗
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
       is_txn_single γtpc tid pid (λ data, key [[γ.(ps_kvs)]]↦{3/4} data.(oldValue)) (λ data, key [[γ.(ps_kvs)]]↦{3/4} (word.add data.(oldValue) amnt)) ∗
       is_participant ps γ γtpc pid
  }}}
    ParticipantServer__PrepareIncrease #ps #tid #key #amnt
  {{{
       (a op oldValue:u64), RET #a; ⌜a ≠ 0⌝ ∨ ⌜a = 0⌝ ∗ prepared γtpc tid pid ∗
       (tid,pid) [[γtpc.(txn_data_gn)]]↦ro Some (mkTransactionC key oldValue op amnt)
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
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Htxns_own Hfinish_tok Hdata_unused]").
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
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Htxns_own Hfinish_tok Hdata_unused]").
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
  iDestruct "Hptsto" as "[[Hphysptsto Hptsto]|Hbad]"; last first.
  { admit. (* conflict Hbad Hkeylocked *) }
  iMod (map_update _ _ (word.add old_v4 amnt) with "[] Hphysptsto") as "[_ Hphysptsto]".
  { admit. }
  iDestruct "Hphysptsto" as "[Hphysptsto Hphysptsto2]".
  iSpecialize ("Hkvs_ctx" $! (λ k, kv_ctx γ (typed_map.map_insert kvsM key (word.add old_v4 amnt)) k)%I with "[] [Hkeylocked Hphysptsto2]").
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
    unfold map_get, typed_map.map_insert.
    rewrite lookup_insert.
    iFrame.
  }

  (* Get finish token *)
  iDestruct (big_sepS_elem_of_acc _ _ tid with "Hfinish_tok") as "[Hfinish_tok Hfinish_rest]".
  { set_solver. }
  iDestruct "Hfinish_tok" as "[%Hbad|Hfinish_tok]".
  { exfalso. admit. (* use Hmapget_finished and Hbad *) }

  (* Get unused data token *)
  iDestruct (big_sepS_elem_of_acc_impl tid with "Hdata_unused") as "[Hdata Hdata_rest]".
  { set_solver. }
  iDestruct  "Hdata" as "[%Hbad|Hdata]".
  { exfalso. admit. (* tid can't be in either txnsM or finishedTxnsM *) }
  iMod (participant_prepare (mkTransactionC key old_v3 (U64 1) amnt) with "Htxn Hfinish_tok [Hptsto] Hdata") as "(#Hprep & Hfinish_tok & #Hdata)".
  { done. }
  {
    rewrite Hmapget_v3 /=.
    iFrame.
  }
  iSpecialize ("Hfinish_rest" with "[Hfinish_tok]").
  { by iRight. }

  wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfinish_rest Hdata_rest Htxns_own Hphysptsto]").
  {
    iNext. iExists _, _, _,_,_,_,_; iFrame "HkvsMap HtxnsMap #∗".
    (* TODO: combine into one big_sepM *)
    iSplitL "".
    { (* Need to have all prepared tokens *)
      iApply big_sepM_insert.
      { apply map_get_false in Hmapget. naive_solver. }
      iFrame "#".
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

Lemma wp_TransactionCoordinator__doTransfer (tc:loc) γtpc (tid acc1 acc2 amount v1 v2:u64) :
  {{{
       TransactionCoordinator_own tc γtpc ∗
       fresh_tid γtpc tid ∗ (* TODO: make this logically-atomic *)
       acc1 [[γ1.(ps_kvs)]]↦{1/4} v1 ∗
       acc2 [[γ2.(ps_kvs)]]↦{1/4} v2
  }}}
    TransactionCoordinator__doTransfer #tc #tid #acc1 #acc2 #amount
  {{{
       RET #();
       acc1 [[γ1.(ps_kvs)]]↦{1/4} (word.add v1 amount) ∗
       acc2 [[γ2.(ps_kvs)]]↦{1/4} (word.sub v2 amount)
  }}}.
Proof.
  iIntros (Φ) "(Hown & Hfresh & Hacc1 & Hacc2) HΦ".
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
    iApply "HΦ".
    rewrite Qp_three_quarter_quarter.
    by iFrame "Hacc1 Hacc2".
  - (* TODO: Abort case *)
    admit.
Admitted.

End tpc_example.
