From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof Require Import lockmap_proof.

Section tpc_example.

Context `{!heapG Σ}.
Context `{!mapG Σ u64 u64}.
Context `{!mapG Σ u64 (option bool)}.
Context `{!mapG Σ (u64*u64) ()}.

Record participant_names :=
mk_participant_names  {
    ps_ghs:list (deletable_heap.gen_heapG u64 bool Σ) ;
    ps_kvs:gname
}.

Record tpc_names :=
mk_tpc_names  {
  committed_gn : gname ; (* tid -> option bool *)
  prepared_gn : gname ;  (* (tid, pid) -> () *)
  finish_token_gn : gname ;
  uncommit_token_gn : gname ;
}.

Implicit Type γtpc : tpc_names.
Implicit Type γ : participant_names.

Definition unprepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ ().
Definition prepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ro ().
Definition finish_token γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(finish_token_gn)]]↦ ().
Definition uncommit_token γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(uncommit_token_gn)]]↦ ().
Definition committed_witness γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(uncommit_token_gn)]]↦ro ().

Definition undecided γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ None.
Definition aborted γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ro Some false.
Definition committed γtpc tid : iProp Σ := tid [[γtpc.(committed_gn)]]↦ro Some true.

Definition tpc_inv_single γtpc tid pid R R' : iProp Σ :=
  unprepared γtpc tid pid ∗ uncommit_token γtpc tid pid ∨
  prepared γtpc tid pid ∗ R ∗ uncommit_token γtpc tid pid ∨
  committed γtpc tid ∗ prepared γtpc tid pid ∗ (R' ∨ finish_token γtpc tid pid) ∨
  aborted γtpc tid ∗ finish_token γtpc tid pid
.

Definition txnSingleN (pid:u64) := nroot .@ "tpc" .@ pid.
Definition is_txn_single γtpc (tid pid:u64) R R': iProp Σ := inv (txnSingleN pid) (tpc_inv_single γtpc tid pid R R').

Lemma participant_prepare E γtpc tid pid R R':
  ↑(txnSingleN pid) ⊆ E →
  is_txn_single γtpc tid pid R R' -∗ finish_token γtpc tid pid-∗ R ={E}=∗ prepared γtpc tid pid ∗ finish_token γtpc tid pid.
Proof.
  intros ?.
  iIntros "His_txn Hfinish_tok HR".
  iInv "His_txn" as "[>[Hunprep Huncommit]|[[>#Hprep Hrest]|[Hcommitted|Haborted]]]" "Htclose".
  {
    (* TODO: don't use auth_map; want just mapUR *)
    iMod (map_freeze with "[] Hunprep") as "[_ #Hprep]".
    { admit. }

    iFrame "Hprep Hfinish_tok".
    iMod ("Htclose" with "[HR Huncommit]"); last done.
    iNext.
    iRight.
    iLeft.
    iFrame "#∗".
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

Definition ps_mu_inv (ps:loc) γ γtpc pid : iProp Σ :=
  ∃ (kvs_ptr txns_ptr finishedTxns_ptr lockMap_ptr:loc) (kvsM:gmap u64 u64) (txnsM:gmap u64 TransactionC)
    (finishedTxnsM:gmap u64 unit),

    "Hkvs" ∷ ps ↦[ParticipantServer.S :: "kvs"] #kvs_ptr ∗
    "Htxns" ∷ ps ↦[ParticipantServer.S :: "txns"] #txns_ptr ∗
    "HfinishedTxns" ∷ ps ↦[ParticipantServer.S :: "finishedTxns"] #finishedTxns_ptr ∗

    "HlockMap_ptr" ∷ ps ↦[ParticipantServer.S :: "lockmap"] #lockMap_ptr ∗
    "HkvsMap" ∷ is_map (kvs_ptr) kvsM ∗
    "HtxnsMap" ∷ is_map (txns_ptr) txnsM ∗
    "HfinishedTxnsMap" ∷ is_map (finishedTxns_ptr) finishedTxnsM ∗

    "Hkvs_ctx" ∷ map_ctx γ.(ps_kvs) 1 kvsM ∗
    "#HlockMap" ∷ is_lockMap lockMap_ptr γ.(ps_ghs) (fin_to_set u64) (λ x, x [[γ.(ps_kvs)]]↦{1/2} (map_get kvsM x).1) ∗

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

(* TODO: One participant shouldn't know the resources that other participants are contributing *)
Lemma wp_PrepareIncrease (ps:loc) tid pid γ γtpc (key key' amnt:u64) :
  {{{
       is_txn_single γtpc tid pid (∃ v:u64, key [[γ.(ps_kvs)]]↦{1/2} v) (∃ v:u64, key' [[γ.(ps_kvs)]]↦{1/2} v) ∗
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
  wp_apply (wp_LockMap__Acquire with "[$HlockMap]").
  { iPureIntro. set_solver. }
  iIntros "[Hptsto Hkeylocked]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v old_v_ok) "[%Hmapget_v HkvsMap]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert _ _ _ _ (mkTransactionC _ _ _ _) with "HtxnsMap").
  { eauto. }
  iIntros "HtxnsMap".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v' ok') "[Hmapget_oldv' HkvsMap]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "HkvsMap").
  { eauto. }
  iIntros "HkvsMap".
  iApply wp_fupd.
  wp_pures.
  iApply "HΦ".

  (* FIXME: lock release missing *)

  iRight.
  iDestruct (big_sepS_elem_of_acc _ _ tid with "Hfinish_tok") as "[Hfinish_tok Hfinish_rest]".
  { set_solver. }
  iDestruct "Hfinish_tok" as "[%Hbad|Hfinish_tok]".
  { admit. (* FIXME: add lookup *) }
  iMod (participant_prepare with "Htxn Hfinish_tok [Hptsto]") as "[#Hprep Hfinish_tok]".
  { done. }
  { iExists _; iFrame. }
  iSpecialize ("Hfinish_rest" with "[Hfinish_tok]").
  { by iRight. }
  iFrame "Hprep".
  by iModIntro.
Admitted.

End tpc_example.
