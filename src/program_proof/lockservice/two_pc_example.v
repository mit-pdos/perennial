From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
Require Import Decimal Ascii String DecimalString.
From Perennial.program_proof.lockservice Require Import grove_ffi.
From Perennial.program_proof Require Import lockmap_proof.

From iris.algebra Require Import excl agree auth gmap csum.

From Perennial.Helpers Require Import Map gset ipm.

From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl agree auth gmap csum.
From iris.bi.lib Require Import fractional.
From Perennial.base_logic.lib Require Import own ghost_map.

Section tpc_example.

(* Protocol:
   Exclusive: Unfinished
   Idempotents: Prepared, Committed, Aborted

   Prepared ⋅ Uncomitted = Uncomitted    <--- Glue
   Unprepared ⋅ Undecided = Invalid    <--- Glue (implied by above)

   Committed ⋅ Undecided = Invalid
   Committed ⋅ DoDecide = Invalid      <---- this is where we would have glued if tokens were separate from state
   Aborted ⋅ DoDecide = Invalid

   Unprepared ∗ DoPrepare ==∗ Uncomitted (== Prepared ∗ Uncommitted)
   Uncommitted ∗ DoDecide ==∗ Committed
   DoDecide ==∗ CoordinatorAborted
   CoordinatorAborted ∗ Unfinished ==∗ Aborted

   Participant owns Unfinished for any tid ∉ finishedTxns
   Participant owns DoPrepare for any tid ∉ (finishedTxns ∪ txnsM)
   Coordinator owns Unprepared for any fresh tid
   Coordinator owns DoDecide for any fresh tid

   is_participant := inv (Unprepared ∨ Undecided ∗ R ∨ Committed ∗ (R' ∨ Finished) ∨ Aborted)

   { is_participant }
     Paricipant__Prepare
   { Prepared }

   { is_participant ∗ Committed }
   Participant__Commit
   { emp }
   { is_participant ∗ Aborted }
   Participant__Abort
 *)


Context `{!heapGS Σ, !lockmapG Σ}.
Definition one_shot_decideR := csumR fracR (agreeR boolO).
(* TODO: too annoying to have both csums in context *)
(* Definition one_shotR := csumR fracR (agreeR unitO). *)
Context `{!inG Σ (gmapUR u64 one_shotR)}.
Context `{!inG Σ (gmapUR u64 one_shot_decideR)}.
Context `{!inG Σ (gmapUR u64 (exclR unitO))}.

Record tpc_names :=
mk_tpc_names  {
  prep_gn: gname ;
  start_gn : gname ;
  commit_gn: gname ;
  abort_gn: gname ;
  finish_gn : gname ;
  unknown_gn : gname ;
}.

Implicit Type γtpc : tpc_names.

Definition unfinished γtpc (tid:u64) : iProp Σ := own γtpc.(finish_gn) {[ tid := Cinl 1%Qp ]}.
Definition never_finish γtpc (tid:u64) : iProp Σ := own γtpc.(finish_gn) {[ tid := Cinr (to_agree true) ]}.
Definition unstarted γtpc (tid:u64) : iProp Σ := own γtpc.(start_gn) {[ tid := Cinl 1%Qp ]}.
Definition never_start γtpc (tid:u64) : iProp Σ := own γtpc.(start_gn) {[ tid := Cinr (to_agree true) ]}.

Definition prepared γtpc (tid:u64) : iProp Σ := own γtpc.(prep_gn) {[ tid := Cinr (to_agree true) ]}.

Definition undecided γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinl (1/2)%Qp) ]} ∗ prepared γtpc tid.
Definition unaborted γtpc (tid:u64) : iProp Σ := own γtpc.(abort_gn) {[ tid := Cinl 1%Qp ]}.
Definition coordinator_neverabort γtpc (tid:u64) : iProp Σ := own γtpc.(abort_gn) {[ tid := (Cinr (to_agree false)) ]}.
Definition do_decide γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinl (1/2)%Qp) ]} ∗ unaborted γtpc tid.
Definition coordinator_aborted γtpc (tid:u64) : iProp Σ := own γtpc.(abort_gn) {[ tid := (Cinr (to_agree true)) ]} ∗ never_start γtpc tid.
Definition committed γtpc (tid:u64) : iProp Σ := own γtpc.(commit_gn) {[ tid := (Cinr (to_agree true)) ]} ∗ coordinator_neverabort γtpc tid ∗ prepared γtpc tid.

Definition unprepared γtpc (tid:u64) : iProp Σ := own γtpc.(prep_gn) {[ tid := (Cinl (1/2)%Qp) ]} ∗ own γtpc.(commit_gn) {[ tid := (Cinl (1/2)%Qp )]}.
Definition do_prepare γtpc (tid:u64) : iProp Σ := own γtpc.(prep_gn) {[ tid := (Cinl (1/2)%Qp) ]}.

Definition aborted γtpc (tid:u64) : iProp Σ := coordinator_aborted γtpc tid ∗ never_finish γtpc tid.

Definition tpc_inv_single γtpc tid R R' : iProp Σ :=
  unprepared γtpc tid ∨
  undecided γtpc tid ∗ (R ∨ unstarted γtpc tid) ∨
  committed γtpc tid ∗ (R' ∨ unfinished γtpc tid) ∨
  aborted γtpc tid
.

Definition txnSingleN := nroot .@ "tpc".
Definition is_txn_single γtpc (tid:u64) R R' : iProp Σ := inv (txnSingleN) (tpc_inv_single γtpc tid R R').

Lemma do_prepare_unprepared γtpc tid :
  do_prepare γtpc tid -∗ unprepared γtpc tid ==∗ undecided γtpc tid.
Proof.
  rewrite /do_prepare /unprepared.
  iIntros "Hprep1 [Hprep2 Hundec]".
  iCombine "Hprep1 Hprep2" as "Hprep".
  rewrite -Cinl_op.
  rewrite frac_op. rewrite Qp_half_half.
  iFrame "Hundec".
  iMod (own_update _ _ _ with "Hprep") as "$".
  {
    apply singleton_update.
    apply cmra_update_exclusive.
    done.
  }
  by iModIntro.
Qed.

Lemma undecided_is_prepared γtpc tid :
  undecided γtpc tid -∗ prepared γtpc tid.
Proof.
  iIntros "[_ $]".
Qed.

Lemma do_prepare_undecided_false γtpc tid :
  do_prepare γtpc tid -∗ undecided γtpc tid -∗ False.
Proof.
  iIntros "Hdoprep [_ Hprep]".
  rewrite /do_prepare /prepared.
  iDestruct (own_valid_2 with "Hdoprep Hprep") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  naive_solver.
Qed.

Lemma do_prepare_committed_false γtpc tid :
  do_prepare γtpc tid -∗ committed γtpc tid -∗ False.
Proof.
  iIntros "Hdoprep (_&_&Hprep)".
  rewrite /do_prepare /prepared.
  iDestruct (own_valid_2 with "Hdoprep Hprep") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  naive_solver.
Qed.

Lemma unfinished_unfinished_false γtpc tid :
  unfinished γtpc tid -∗ unfinished γtpc tid -∗ False.
Proof.
  iIntros.
  iDestruct (own_valid_2 with "[$] [$]") as %Hbad.
  exfalso. rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  done.
Qed.

Lemma unfinished_aborted_false γtpc tid :
  unfinished γtpc tid -∗ aborted γtpc tid -∗ False.
Proof.
  iIntros "Hunfinish [_ Hunfinish2]".
  rewrite /unfinished.
  rewrite /never_finish.
  iDestruct (own_valid_2 with "Hunfinish2 Hunfinish") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  setoid_rewrite singleton_valid in Hbad.
  done.
Qed.

Lemma unfinished_coord_aborted_abort γtpc tid :
  unfinished γtpc tid -∗ coordinator_aborted γtpc tid ==∗ aborted γtpc tid.
Proof.
  iIntros "Hunfinish $".
  iApply (own_update with "Hunfinish").
  apply singleton_update.
  eapply cmra_update_exclusive.
  done.
Qed.

Lemma unprepared_prepared_false γtpc tid :
  unprepared γtpc tid -∗ prepared γtpc tid -∗ False.
Proof.
  iIntros "[Hunprep _] Hprep".
  iDestruct (own_valid_2 with "Hunprep Hprep") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  naive_solver.
Qed.

Lemma committed_coordinator_aborted γtpc tid :
  committed γtpc tid -∗ coordinator_aborted γtpc tid -∗ False.
Proof.
  iIntros "(_&Hnoabort&_) [Habort _]".
  iDestruct (own_valid_2 with "Hnoabort Habort") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  rewrite -Cinr_op in Hbad.
  setoid_rewrite Cinr_valid in Hbad.
  setoid_rewrite to_agree_op_valid in Hbad.
  naive_solver.
Qed.

Lemma coordinator_aborted_unstarted_false γtpc tid :
  coordinator_aborted γtpc tid -∗ unstarted γtpc tid -∗ False.
Proof.
  iIntros "[_ Hnostart] Hstart".
  iDestruct (own_valid_2 with "Hnostart Hstart") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  done.
Qed.

Lemma unprepared_committed_false γtpc tid :
  unprepared γtpc tid -∗ committed γtpc tid -∗ False.
Proof.
  iIntros "Hunprep (_&_&Hprep)".
  iApply (unprepared_prepared_false with "Hunprep Hprep").
Qed.

Lemma undecided_committed_false γtpc tid :
  undecided γtpc tid -∗ committed γtpc tid -∗ False.
Proof.
  iIntros "[Hundec _] (Hcom&_&_)".
  iDestruct (own_valid_2 with "Hundec Hcom") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  done.
Qed.

Lemma do_commit γtpc tid :
  do_decide γtpc tid -∗ undecided γtpc tid ==∗ committed γtpc tid.
Proof.
  iIntros "[Hdodec Hunabort] [Hundec $]".
  iCombine "Hdodec Hundec" as "Hdec".
  rewrite -Cinl_op frac_op Qp_half_half.
  iSplitL "Hdec".
  {
    iApply (own_update with "Hdec").
    apply singleton_update.
    apply cmra_update_exclusive.
    done.
  }
  {
    iApply (own_update with "Hunabort").
    apply singleton_update.
    apply cmra_update_exclusive.
    done.
  }
Qed.

Lemma do_decide_committed_false γtpc tid :
  do_decide γtpc tid -∗ committed γtpc tid -∗ False.
Proof.
  iIntros "[Hundec _] [Hcom _]".
  iDestruct (own_valid_2 with "Hundec Hcom") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  done.
Qed.

Lemma do_decide_aborted_false γtpc tid :
  do_decide γtpc tid -∗ aborted γtpc tid -∗ False.
Proof.
  iIntros "[_ Hunabort] [[Habort _] _]".
  iDestruct (own_valid_2 with "Hunabort Habort") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  done.
Qed.

Lemma unstarted_unstarted_false γtpc tid :
  unstarted γtpc tid -∗ unstarted γtpc tid -∗ False.
Proof.
  iIntros.
  iDestruct (own_valid_2 with "[$] [$]") as %Hbad.
  exfalso.
  rewrite singleton_op in Hbad.
  apply singleton_valid in Hbad.
  done.
Qed.

Lemma do_abort γtpc tid :
  do_decide γtpc tid -∗ unstarted γtpc tid ==∗ coordinator_aborted γtpc tid.
Proof.
  iIntros "[_ Hunabort] Hunstart".
  iSplitR "Hunstart".
  {
    iApply (own_update with "Hunabort").
    apply singleton_update.
    apply cmra_update_exclusive.
    done.
  }
  {
    iApply (own_update with "Hunstart").
    apply singleton_update.
    apply cmra_update_exclusive.
    done.
  }
Qed.

Lemma participant_prepare E γtpc tid R R':
  ↑(txnSingleN) ⊆ E →
  is_txn_single γtpc tid R R' -∗ ▷R -∗ do_prepare γtpc tid -∗ unfinished γtpc tid ={E}=∗
  prepared γtpc tid ∗ unfinished γtpc tid.
Proof.
  iIntros (?) "#His_txn HR Hdoprep Hunfinished".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>Hunprep|Ht]".
  {
    iDestruct (do_prepare_unprepared with "Hdoprep Hunprep") as ">Hundec".
    iDestruct (undecided_is_prepared with "Hundec") as "#$".
    iMod ("Htclose" with "[HR Hundec]"); last by iFrame.
    iRight. iLeft. iFrame.
  }
  iDestruct "Ht" as "[[>Hundec _]|Ht]".
  { iExFalso. iApply (do_prepare_undecided_false with "[$] [$]"). }
  iDestruct "Ht" as "[[>#Hcommit _]|Ht]".
  { iExFalso. iApply (do_prepare_committed_false with "[$] [$]"). }
  iDestruct "Ht" as ">Habort".
  { iExFalso. iApply (unfinished_aborted_false with "[$] [$]"). }
Qed.

Lemma prepared_participant_abort E γtpc tid R R':
  ↑(txnSingleN) ⊆ E →
  is_txn_single γtpc tid R R' -∗
  unfinished γtpc tid -∗ coordinator_aborted γtpc tid -∗ prepared γtpc tid ={E}=∗
  ▷ R.
Proof.
  intros Hnamespace.
  iIntros "#His_prep Hunfinished #Hcoordabort #Hprepared".
  iInv "His_prep" as "Hp" "Hpclose".
  iDestruct "Hp" as "[>Hunprep|Hp]".
  { iExFalso. iApply (unprepared_prepared_false with "Hunprep Hprepared"). }
  iDestruct "Hp" as "[[>_ HR]|Hp]".
  {
    iMod (unfinished_coord_aborted_abort with "Hunfinished Hcoordabort") as "#?".
    iMod ("Hpclose" with "[]") as "_".
    { iRight; iRight. iRight. iFrame "#∗". }
    iDestruct "HR" as "[$|>?]"; first by iModIntro.
    iExFalso. iApply coordinator_aborted_unstarted_false; eauto.
  }
  iDestruct "Hp" as "[[>#Hcommit _]|Hp]".
  { iExFalso. iApply committed_coordinator_aborted; eauto. }
  iDestruct "Hp" as ">#Habort".
  { iExFalso. iApply (unfinished_aborted_false with "[$] [$]"). }
Qed.

Lemma prepared_participant_finish_commit E γtpc tid R R':
  ↑(txnSingleN) ⊆ E →
  is_txn_single γtpc tid R R' -∗ committed γtpc tid -∗ unfinished γtpc tid ={E}=∗
  ▷ R'.
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hcommit Hunfinished".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>Hunprep|Ht]".
  { iExFalso. iApply (unprepared_committed_false with "[$] [$]"). }
  iDestruct "Ht" as "[[>Hundec _]|Ht]".
  { iExFalso. iApply (undecided_committed_false with "[$] [$]"). }
  iDestruct "Ht" as "[[_ HRfinish]|Ht]".
  {
    iDestruct "HRfinish" as "[HR' | >HRfinish]"; last first.
    { iExFalso. iApply (unfinished_unfinished_false with "Hunfinished HRfinish"). }
    iFrame.
    iMod ("Htclose" with  "[Hunfinished]"); last by iModIntro.
    iRight; iRight; iLeft; iFrame "#∗".
  }
  iDestruct "Ht" as ">#Habort".
  { iExFalso. iApply (unfinished_aborted_false with "[$] [$]"). }
Qed.

Lemma prepared_participant_start_commit E γtpc tid R R':
  ↑(txnSingleN) ⊆ E →
  is_txn_single γtpc tid R R' -∗ prepared γtpc tid -∗ do_decide γtpc tid -∗ unstarted γtpc tid ={E}=∗
  ▷ R ∗ (▷ R' ={E}=∗ committed γtpc tid).
Proof.
  intros Hnamespace.
  iIntros "#His_txn #Hprep Hdodec Hunstarted".
  iInv "His_txn" as "Ht" "Htclose".
  iDestruct "Ht" as "[>Hunprep|Ht]".
  { iExFalso. iApply (unprepared_prepared_false with "[$] [$]"). }
  iDestruct "Ht" as "[[>Hundec HR]|Ht]".
  {
    iDestruct "HR" as "[$|>Hunstarted2]".
    {
      iMod ("Htclose" with "[Hundec Hunstarted]").
      {
        iNext. iRight. iLeft. iFrame "Hundec". iRight. iFrame.
      }
      iModIntro.
      iIntros "HR'".
      iInv "His_txn" as "Ht" "Htclose".
      iDestruct "Ht" as "[>Hunprep|Ht]".
      { iExFalso. iApply (unprepared_prepared_false with "[$] [$]"). }
      iDestruct "Ht" as "[[>Hundec HR]|Ht]".
      {
        iMod (do_commit with "Hdodec Hundec") as "#$".
        iMod ("Htclose" with "[HR']"); last by iModIntro.
        iRight; iRight; iLeft. iFrame "#∗".
      }
      iDestruct "Ht" as "[[#>Hcommitted _]|Ht]".
      { iExFalso. iApply (do_decide_committed_false with "[$] [$]"). }
      iDestruct "Ht" as ">#Habort".
      { iExFalso. iApply (do_decide_aborted_false with "[$] [$]"). }
    }
    { iExFalso. iApply (unstarted_unstarted_false with "[$] [$]"). }
  }
  iDestruct "Ht" as "[[#>Hcommitted _]|Ht]".
  { iExFalso. iApply (do_decide_committed_false with "[$] [$]"). }
  iDestruct "Ht" as ">#Habort".
  { iExFalso. iApply (do_decide_aborted_false with "[$] [$]"). }
Qed.

(* TODO: define these *)
Definition txn_unknown γtpc (tid:u64) : iProp Σ := own γtpc.(unknown_gn) {[ tid := Cinl (1)%Qp ]}.
Definition txn_unknown_is γtpc (tid x:u64) : iProp Σ := own γtpc.(unknown_gn) {[ tid := Cinr (to_agree true) ]}.

Lemma txn_unknown_choose x γtpc tid:
  txn_unknown γtpc tid ==∗ txn_unknown_is γtpc tid x.
Admitted.

Definition is_txn_single_unknown γtpc (tid:u64) R R' : iProp Σ := is_txn_single γtpc tid
  (∃ x, R x ∗ txn_unknown_is γtpc tid x)%I
  (∃ x, R' x ∗ txn_unknown_is γtpc tid x)%I
.

Lemma txn_unknown_is_agree γtpc tid x y:
  txn_unknown_is γtpc tid x -∗ txn_unknown_is γtpc tid y -∗ ⌜x = y⌝.
Admitted.

(* Proof of participant code *)
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

Record participant_names :=
mk_participant_names  {
    ps_tpc:tpc_names ;
    ps_ghs:list gname ;
    ps_kvs:gname ;
    ps_kv_toks:gname
}.

Implicit Type γ : participant_names.

Definition kv_ctx γ (kvsM:gmap u64 u64) k : iProp Σ :=
  k [[γ.(ps_kvs)]]↦{3/4} (map_get kvsM k).1 ∨
  (Locked γ.(ps_ghs) k).

Definition kv_tok γ (k:u64) : iProp Σ :=
  own γ.(ps_kv_toks) {[ k := Excl() ]}.

Lemma kv_tok_2_false γ k:
  kv_tok γ k -∗ kv_tok γ k -∗ False.
Admitted.

Definition ps_mu_inv (ps:loc) γ : iProp Σ :=
  ∃ (kvs_ptr txns_ptr finishedTxns_ptr lockMap_ptr:loc) (kvsM:gmap u64 u64) (txnsM:gmap u64 TxnResourcesC)
    (finishedTxnsM:gmap u64 bool),

    "Hkvs" ∷ ps ↦[ParticipantServer :: "kvs"] #kvs_ptr ∗
    "Htxns" ∷ ps ↦[ParticipantServer :: "txns"] #txns_ptr ∗
    "HfinishedTxns" ∷ ps ↦[ParticipantServer :: "finishedTxns"] #finishedTxns_ptr ∗

    "HlockMap_ptr" ∷ ps ↦[ParticipantServer :: "lockmap"] #lockMap_ptr ∗
    "HkvsMap" ∷ is_map (kvs_ptr) kvsM ∗
    "HtxnsMap" ∷ is_map (txns_ptr) txnsM ∗
    "HfinishedTxnsMap" ∷ is_map (finishedTxns_ptr) finishedTxnsM ∗

    "Hkvs_ctx" ∷ ([∗ set] k ∈ (fin_to_set u64), kv_ctx γ kvsM k) ∗
    "#HlockMap" ∷ is_lockMap lockMap_ptr γ.(ps_ghs) (fin_to_set u64) (λ k, kv_tok γ k) ∗

    "#Htxns_prop_pers" ∷ ([∗ map] tid ↦ txn ∈ txnsM, prepared γ.(ps_tpc) tid ∗ (∃ x, txn_unknown_is γ.(ps_tpc) tid x)) ∗
    (* TODO: need to add post-abort resources *)
    "Htxns_postcommit" ∷ ([∗ map] tid ↦ txn ∈ txnsM, kv_tok γ txn.(key) ∗ ((committed γ.(ps_tpc) tid ={⊤}=∗ (txn.(key) [[γ.(ps_kvs)]]↦{3/4} (map_get kvsM txn.(key)).1)) ∧ (coordinator_aborted γ.(ps_tpc) tid ={⊤}=∗ (txn.(key) [[γ.(ps_kvs)]]↦{3/4} txn.(oldValue))))) ∗
    "Hfreshtxns" ∷ ([∗ set] tid ∈ (fin_to_set u64), (⌜tid ∈ dom (gset u64) finishedTxnsM⌝ ∨ ⌜tid ∈ dom (gset u64) txnsM⌝ ∨ (do_prepare γ.(ps_tpc) tid ∗ unfinished γ.(ps_tpc) tid ∗ txn_unknown γ.(ps_tpc) tid))) ∗
    "%" ∷ ⌜(dom (gset u64) txnsM) ## dom (gset u64) finishedTxnsM⌝
.

Definition participantN := nroot .@ "participant".

Definition is_participant (ps:loc) γ : iProp Σ :=
  ∃ (mu:loc),
  "#Hmu" ∷ readonly (ps ↦[ParticipantServer :: "mu"] #mu) ∗
  "#Hmu_inv" ∷ is_lock participantN #mu (ps_mu_inv ps γ)
.

Lemma txn_single_forget_unknown γ tid R R' x :
  is_txn_single_unknown γ.(ps_tpc) tid R R' -∗
  txn_unknown_is γ.(ps_tpc) tid x -∗
  is_txn_single γ.(ps_tpc) tid (R x) (R' x)
.
Proof using Type*.
  iIntros "? #Hunknown".
  iApply (inv_alter with "[$]").
  repeat iModIntro.
  iIntros "Hi".
  iSplitR "".
  {
    iDestruct "Hi" as "[Hunprep|Hi]".
    { iLeft. iFrame. }
    iDestruct "Hi" as "[Hundec|Hi]".
    { iRight. iLeft. iDestruct "Hundec" as "[$ [Hundec|$]]".
      iLeft.
      iDestruct "Hundec" as (?) "[HR #Hunknown2]".
      iDestruct (txn_unknown_is_agree with "Hunknown Hunknown2") as %Hre.
      rewrite Hre.
      iFrame.
    }
    iDestruct "Hi" as "[Hcom|$]".
    {
      iRight. iRight. iLeft.
      iDestruct "Hcom" as "[$ [HR'|$]]".
      iLeft.
      iDestruct "HR'" as (?) "[HR' #Hunknown2]".
      iDestruct (txn_unknown_is_agree with "Hunknown Hunknown2") as %->.
      iFrame.
    }
  }
  {
    iIntros "Hi".
    iDestruct "Hi" as "[$|Hi]".
    iDestruct "Hi" as "[Hundec|Hi]".
    {
      iRight; iLeft. iDestruct "Hundec" as "[$ [HR|$]]".
      iLeft. iExists _; iFrame "#∗".
    }
    iDestruct "Hi" as "[Hcom|$]".
    {
      iRight; iRight; iLeft. iDestruct "Hcom" as "[$ [HR|$]]".
      iLeft. iExists _; iFrame "#∗".
    }
  }
Qed.

Lemma lockmap_locked_locked_false (ghs:list gname) k :
  Locked ghs k -∗ Locked ghs k -∗ False.
Proof.
  iIntros "P Q".
  rewrite /Locked.
  iDestruct "P" as (? HP) "P".
  iDestruct "Q" as (? HQ) "Q".
  rewrite HQ in HP.
  replace (gh) with (gh0) by naive_solver.
  rewrite /lockmap_proof.locked.
  iCombine "P Q" as "P".
  iDestruct (ghost_map_elem_valid with "P") as %Hbad.
  done.
Qed.

Lemma wp_Participant__PrepareIncrease (ps:loc) tid γ (key amnt:u64) :
  {{{
       is_participant ps γ ∗
       is_txn_single_unknown γ.(ps_tpc) tid (λ ov, key [[γ.(ps_kvs)]]↦{3/4} ov) (λ ov, key [[γ.(ps_kvs)]]↦{3/4} (word.add ov amnt))
  }}}
    ParticipantServer__PrepareIncrease #ps #tid #key #amnt
  {{{
       (a:u64), RET #a; ⌜a ≠ 0⌝ ∨ (⌜a = 0⌝ ∗ prepared γ.(ps_tpc) tid ∗
       ∃ ov, is_txn_single γ.(ps_tpc) tid (key [[γ.(ps_kvs)]]↦{3/4} ov) (key [[γ.(ps_kvs)]]↦{3/4} (word.add ov amnt))
       )
  }}}.
Proof.
  iIntros (Φ) "[#Hps #Htxn] HΦ".
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
    apply map_get_true in Hmapget.
    iDestruct (big_sepM_lookup_acc with "Htxns_prop_pers") as "[[Hprep Hunknown] _]".
    { done. }
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfreshtxns Htxns_postcommit]").
    {
      iNext. iExists _, _, _,_,_,_,_; iFrame "#∗".
      done.
    }
    wp_pures.
    iApply "HΦ".
    iRight. iFrame "#".
    iSplitL ""; first done.
    iDestruct "Hunknown" as (x) "Hunknown".
    iExists x.
    iApply (txn_single_forget_unknown with "Htxn Hunknown").
  }
  wp_loadField.
  wp_apply (wp_MapGet with "HfinishedTxnsMap").
  iIntros (vfinished okFinished) "[%Hmapget_finished HfinishedTxnsMap]".
  wp_pures.
  wp_if_destruct.
  { (* Transaction already finished *)
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfreshtxns Htxns_postcommit]").
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
  iIntros "[Hktok Hkeylocked]".
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
    wp_loadField. wp_apply (wp_LockMap__Release with "[$HlockMap $Hkeylocked $Hktok]").
    wp_pures.
    wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfreshtxns Htxns_postcommit]").
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
  { done. }
  iIntros "HtxnsMap".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapGet with "HkvsMap").
  iIntros (old_v4 ok4) "[%Hmapget_oldv4 HkvsMap]".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "HkvsMap").
  { done. }
  iIntros "HkvsMap".
  wp_pures.

  iDestruct (big_sepS_elem_of_acc_impl key with "Hkvs_ctx") as "[Hptsto Hkvs_ctx]".
  { set_solver. }
  iDestruct "Hptsto" as "[Hptsto|Hbad]"; last first.
  { iExFalso.
    iApply (lockmap_locked_locked_false with "[$] [$]"). }
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

  (* Get unused unfinished token *)
  iDestruct (big_sepS_elem_of_acc_impl tid with "Hfreshtxns") as "[Hfreshtxn Hfreshtxns]".
  { set_solver. }
  iDestruct "Hfreshtxn" as "[%Hbad|Hfreshtxn]".
  { exfalso. apply map_get_false in Hmapget_finished as [Hbad2 _].
    apply (not_elem_of_dom finishedTxnsM) in Hbad2. set_solver. }
  iDestruct "Hfreshtxn" as "[%Hbad|Hfreshtxn]".
  { exfalso. apply map_get_false in Hmapget as [Hbad2 _].
    apply (not_elem_of_dom txnsM) in Hbad2. set_solver. }
  iDestruct "Hfreshtxn" as "(Hdoprep & Hunfinish & Hunknown)".
  iMod (txn_unknown_choose with "Hunknown") as "#Hunknown".
  iMod (participant_prepare with "Htxn [Hptsto] Hdoprep Hunfinish") as "[#His_prep Hunfinish]".
  { done. }
  { iNext. iExists _; iFrame "Hptsto". iFrame "Hunknown". }
  wp_loadField. wp_apply (release_spec with "[$Hmu_inv $Hmulocked Hkvs Htxns HfinishedTxns HlockMap_ptr HkvsMap HtxnsMap HfinishedTxnsMap Hkvs_ctx Hfreshtxns Hktok Htxns_postcommit Hunfinish]").
  {
    iNext. iExists _, _, _,_,_,_,_; iFrame "HkvsMap HtxnsMap #∗".
    iSplitL "".
    { (* Need to have all prepared witnesses *)
      iApply big_sepM_insert.
      { apply map_get_false in Hmapget. naive_solver. }
      rewrite Hmapget_v3.
      simpl.
      iFrame "His_prep".
      iSplitL "".
      { iExists _; iFrame "#". }
      iApply (big_sepM_impl with "Htxns_prop_pers").
      iModIntro. iIntros.
      iFrame "#".
    }
    iSplitL "Htxns_postcommit Hktok Hunfinish".
    { (* Need to have local lock on key and post-commit resources for all in-progress txns *)
      iAssert (∀ tid txn, ⌜txnsM !! tid = Some txn⌝ → ⌜txn.(tpc_example.key) = key⌝ → False)%I with "[Hktok Htxns_postcommit]" as %Hnewkey.
      {
        iIntros (tid2 txn2 ? ?).
        iDestruct (big_sepM_lookup_acc _ _ tid2 with "Htxns_postcommit") as "[[Hktok2 _] _]".
        { done. }
        rewrite H1.
        iApply (kv_tok_2_false with "[$] [$]").
      }
      rewrite /typed_map.map_insert.
      iApply (big_sepM_insert_2 with "[Hktok Hunfinish] [Htxns_postcommit]").
      {
        rewrite Hmapget_v3.
        simpl.
        iFrame.
        replace (old_v4) with (old_v3); last first.
        { rewrite Hmapget_v3 in Hmapget_oldv4.
          naive_solver. }
        iIntros.
        iSplit.
        { (* prove post-commit resources *)
          rewrite lookup_insert /=.
          iIntros.
          iMod (prepared_participant_finish_commit with "Htxn [$] Hunfinish") as "HR'".
          { done. }
          iMod "HR'".
          iDestruct "HR'" as (?) "[Hkey #Hunknown2]".
          iDestruct (txn_unknown_is_agree with "Hunknown Hunknown2") as %->.
          iFrame. by iModIntro.
        }
        { (* prove post-abort resources *)
          iIntros.
          iMod (prepared_participant_abort with "Htxn Hunfinish [$] [$]") as "HR'".
          { done. }
          iMod "HR'".
          iDestruct "HR'" as (?) "[Hkey #Hunknown2]".
          iDestruct (txn_unknown_is_agree with "Hunknown Hunknown2") as %->.
          iFrame. by iModIntro.
        }
      }
      {
        iApply (big_sepM_impl with "Htxns_postcommit").
        iModIntro. iIntros.
        rewrite /map_get. simpl.
        rewrite lookup_insert_ne; last first.
        { set_solver. }
        iFrame.
      }
    }
    iSplitL "Hfreshtxns".
    {
      iApply "Hfreshtxns".
      {
        iModIntro.
        iIntros (???) "[%Hcase|[%Hcase|Hcase]]".
        - iLeft. iPureIntro. done.
        - iRight; iLeft. iPureIntro.
          unfold typed_map.map_insert.
          rewrite dom_insert. set_solver.
        - iRight; iRight. iFrame.
      }
      {
        iRight; iLeft. iPureIntro. unfold typed_map.map_insert.
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
  iApply wp_fupd.
  wp_pures.
  iApply "HΦ".
  iFrame "His_prep".
  iRight.
  iSplitL ""; first done.
  iExists ((map_get kvsM key).1).
  iApply (txn_single_forget_unknown with "Htxn Hunknown").
  (* TODO: specializing kv_ctx caused this to show up *)
  Unshelve.
  { apply _. }
  { apply _. }
(* Qed. *)
Admitted.

Lemma wp_Participant__Commit (ps:loc) tid γ :
  {{{
       is_participant ps γ ∗
       committed γ.(ps_tpc) tid
  }}}
    ParticipantServer__Commit #ps #tid
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros (Φ) "(#His_part & #Hcom) HΦ".
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
    wp_loadField. wp_apply (release_spec with "[- HΦ]").
    {
      iFrame "#∗".
      iNext. iExists _, _, _,_,_,_,_; iFrame "#∗".
      done.
    }
    wp_pures.
    by iApply "HΦ".
  }
  (* Found a transaction with that ID *)
  wp_loadField.

  apply map_get_true in Hmapget_txn.
  iDestruct (big_sepM_delete with "Htxns_postcommit") as "[Hpostcommit Htxns_postcommit]".
  { done. }
  iDestruct "Hpostcommit" as "[Hktok Hfupd]".
  iDestruct (big_sepM_lookup_acc _ _ tid with "Htxns_prop_pers") as "[[_ Hdata] _]".
  { done. }
  iMod ("Hfupd" with "Hcom") as "Hptsto".

  iDestruct (big_sepS_elem_of_acc _ _ txn1.(key) with "Hkvs_ctx") as "[Hkv Hkvs_rest]".
  { set_solver. }
  unfold kv_ctx.
  iDestruct "Hkv" as "[Hbad|Hkvlocked]".
  {
    iDestruct (ptsto_mut_agree_frac_value with "Hbad Hptsto") as %[_ Hbad].
    exfalso.
    contradiction.
  }
  iSpecialize ("Hkvs_rest" with "[Hptsto]").
  {
    iLeft.
    iFrame.
  }

  wp_apply (wp_LockMap__Release with "[$HlockMap $Hkvlocked $Hktok]").
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapDelete with "HtxnsMap").
  iIntros "HtxnsMap".
  wp_loadField.
  wp_apply (wp_MapInsert with "HfinishedTxnsMap").
  { done. }
  iIntros "HfinishedTxnsMap".
  wp_pures.
  wp_loadField. wp_apply (release_spec with "[- HΦ]").
  {
    iFrame "Hmu_inv Hmulocked".
    iNext. iExists _, _, _,_,_,_,_; iFrame "HtxnsMap HfinishedTxnsMap ∗#".
    iSplitL "".
    {
      rewrite /map_del.
      iDestruct (big_sepM_delete _ _ tid with "Htxns_prop_pers") as "[_ $]".
      done.
    }
    iSplitL "Hfreshtxns".
    {
      iApply (big_sepS_impl with "Hfreshtxns").
      iModIntro. iIntros (??) "H".
      unfold typed_map.map_insert.
      unfold map_del.
      iDestruct "H" as "[%Hcase|H]".
      { iLeft. iPureIntro. rewrite dom_insert. set_solver. }
      iDestruct "H" as "[%Hcase|H]".
      {
        enough (x ∈ dom (gset u64) (<[tid:=true]> finishedTxnsM)
        ∨ x ∈ dom (gset u64) (delete tid txnsM)).
        { naive_solver. }
        rewrite dom_insert dom_delete.
        destruct (bool_decide (x = tid)) as [|] eqn:X.
        {
          apply bool_decide_eq_true in X.
          set_solver.
        }
        {
          apply bool_decide_eq_false in X.
          set_solver.
        }
      }
      iRight; iRight. iFrame.
    }
    iPureIntro.
    rewrite dom_insert dom_delete.
    set_solver.
  }
  by iApply "HΦ".
Qed.

Lemma wp_Participant__Abort (ps:loc) tid γ :
  {{{
       is_participant ps γ ∗
       coordinator_aborted γ.(ps_tpc) tid
  }}}
    ParticipantServer__Abort #ps #tid
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros (Φ) "(#His_part & #Habort) HΦ".
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
    wp_loadField. wp_apply (release_spec with "[- HΦ]").
    {
      iFrame "#∗".
      iNext. iExists _, _, _,_,_,_,_; iFrame "#∗".
      done.
    }
    wp_pures.
    by iApply "HΦ".
  }
  (* Found a transaction with that ID *)
  wp_loadField.

  apply map_get_true in Hmapget_txn.
  iDestruct (big_sepM_delete with "Htxns_postcommit") as "[Hpostcommit Htxns_postcommit]".
  { done. }
  iDestruct "Hpostcommit" as "[Hktok Hfupd]".
  iDestruct (big_sepM_lookup_acc _ _ tid with "Htxns_prop_pers") as "[[_ Hdata] _]".
  { done. }
  iMod ("Hfupd" with "Habort") as "Hptsto".

  iDestruct (big_sepS_elem_of_acc_impl txn1.(key) with "Hkvs_ctx") as "[Hkv Hkvs_rest]".
  { set_solver. }
  unfold kv_ctx.
  iDestruct "Hkv" as "[Hbad|Hkvlocked]".
  {
    iDestruct (ptsto_mut_agree_frac_value with "Hbad Hptsto") as %[_ Hbad].
    exfalso.
    contradiction.
  }


  iAssert (∀ tid' txn, ⌜delete tid txnsM !! tid' = Some txn⌝ → ⌜txn.(tpc_example.key) = txn1.(key)⌝ → False)%I with "[Hktok Htxns_postcommit]" as %Hnewkey.
  {
    iIntros (tid2 txn2 ? ?).
    iDestruct (big_sepM_lookup_acc _ _ tid2 with "Htxns_postcommit") as "[[Hktok2 _] _]".
    { done. }
    rewrite H1.
    iApply (kv_tok_2_false with "[$] [$]").
  }

  wp_apply (wp_MapInsert with "HkvsMap").
  { done. }
  iIntros "HkvsMap".
  wp_pures.

  wp_loadField.

  wp_apply (wp_LockMap__Release with "[$HlockMap $Hkvlocked $Hktok]").
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapDelete with "HtxnsMap").
  iIntros "HtxnsMap".
  wp_loadField.
  wp_apply (wp_MapInsert with "HfinishedTxnsMap").
  { done. }
  iIntros "HfinishedTxnsMap".
  wp_pures.
  wp_loadField. wp_apply (release_spec with "[- HΦ]").
  {
    iFrame "Hmu_inv Hmulocked".
    iNext. iExists _, _, _,_,_,_,_; iFrame "HtxnsMap HfinishedTxnsMap ∗#".
    iSplitL "Hptsto Hkvs_rest".
    {
      iApply "Hkvs_rest"; last first.
      {
        iLeft. rewrite /typed_map.map_insert. rewrite /map_get. simpl. rewrite lookup_insert.
        simpl. iFrame.
      }
      iModIntro.
      iIntros (???) "[H|$]".
      iLeft.
      rewrite /map_get. rewrite lookup_insert_ne; last done. iFrame.
    }
    iSplitL "".
    {
      rewrite /map_del.
      iDestruct (big_sepM_delete _ _ tid with "Htxns_prop_pers") as "[_ $]".
      done.
    }
    iSplitL "Htxns_postcommit".
    {
      rewrite /map_del.
      iApply (big_sepM_impl with "Htxns_postcommit").
      iModIntro.
      iIntros.
      rewrite /map_get.
      rewrite lookup_insert_ne; last first.
      { naive_solver. }
      iFrame.
    }
    iSplitL "Hfreshtxns".
    {
      iApply (big_sepS_impl with "Hfreshtxns").
      iModIntro. iIntros (??) "H".
      unfold typed_map.map_insert.
      unfold map_del.
      iDestruct "H" as "[%Hcase|H]".
      { iLeft. iPureIntro. rewrite dom_insert. set_solver. }
      iDestruct "H" as "[%Hcase|H]".
      {
        enough (x ∈ dom (gset u64) (<[tid:=true]> finishedTxnsM)
        ∨ x ∈ dom (gset u64) (delete tid txnsM)).
        { naive_solver. }
        rewrite dom_insert dom_delete.
        destruct (bool_decide (x = tid)) as [|] eqn:X.
        {
          apply bool_decide_eq_true in X.
          set_solver.
        }
        {
          apply bool_decide_eq_false in X.
          set_solver.
        }
      }
      iRight; iRight. iFrame.
    }
    iPureIntro.
    rewrite dom_insert dom_delete.
    set_solver.
  }
  by iApply "HΦ".
(* Qed. *)
Admitted.

Variable s0:loc.
Variable s1:loc.
Variables γ1:participant_names.
Variables γ2:participant_names.

Definition TransactionCoordinator_own (tc:loc) : iProp Σ :=

  "#His_part1" ∷ is_participant s0 γ1 ∗
  "#His_part2" ∷ is_participant s1 γ2 ∗
  "Hs0" ∷ tc ↦[TransactionCoordinator :: "s0"] #s0 ∗
  "Hs1" ∷ tc ↦[TransactionCoordinator :: "s1"] #s1
.

Lemma wp_Participant__PrepareDecrease (ps:loc) tid γ γtpc (key amnt:u64) :
  {{{
       is_txn_single_unknown γtpc tid (λ ov, key [[γ.(ps_kvs)]]↦{3/4} ov) (λ ov, key [[γ.(ps_kvs)]]↦{3/4} (word.sub ov amnt)) ∗
       is_participant ps γ
  }}}

    ParticipantServer__PrepareDecrease #ps #tid #key #amnt
  {{{
       (a:u64), RET #a; ⌜a ≠ 0⌝ ∨ ⌜a = 0⌝ ∗ prepared γtpc tid ∗
       ∃ ov, is_txn_single γ.(ps_tpc) tid (key [[γ.(ps_kvs)]]↦{3/4} ov) (key [[γ.(ps_kvs)]]↦{3/4} (word.sub ov amnt))
  }}}.
Proof.
  (* Copy/paste proof from above... *)
Admitted.

Lemma txn_single_alloc γtpc tid R R' :
  unprepared γtpc tid
  ={⊤}=∗
  is_txn_single_unknown γtpc tid R R'.
Proof.
  iIntros.
  iApply (inv_alloc).
  iLeft. iFrame.
Qed.

Definition fresh_tid γtpc tid: iProp Σ := unprepared γtpc tid ∗ do_decide γtpc tid ∗ unstarted γtpc tid.

Lemma wp_TransactionCoordinator__doTransfer {Eo Ei} (tc:loc) (tid acc1 acc2 amount v1 v2:u64) :
Eo ⊆ ⊤ ∖ ↑txnSingleN →
  {{{
       TransactionCoordinator_own tc ∗
       fresh_tid γ1.(ps_tpc) tid ∗
       fresh_tid γ2.(ps_tpc) tid ∗
       |={Eo,Ei}=> (acc1 [[γ1.(ps_kvs)]]↦{1/4} v1 ∗ acc2 [[γ2.(ps_kvs)]]↦{1/4} v2) ∗
        ((acc1 [[γ1.(ps_kvs)]]↦{1/4} (word.add v1 amount) ∗ acc2 [[γ2.(ps_kvs)]]↦{1/4} (word.sub v2 amount)) ={Ei,Eo}=∗ emp)
  }}}
    TransactionCoordinator__doTransfer #tc #tid #acc1 #acc2 #amount
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros (? Φ) "(Hown & Hfresh1 & Hfresh2 & Hacc_pre) HΦ".
  iNamed "Hown".

  iDestruct "Hfresh1" as "(Hunprep1 & Hdodec1 & Hunstart1)".
  iMod (txn_single_alloc  with "Hunprep1") as "#Htxn1".
  iDestruct "Hfresh2" as "(Hunprep2 & Hdodec2 & Hunstart2)".
  iMod (txn_single_alloc  with "Hunprep2") as "#Htxn2".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (wp_Participant__PrepareIncrease with "[]").
  { iFrame "His_part1".
    iFrame "Htxn1".
  }
  iIntros (prepared1) "Hprep1".
  wp_pures.
  wp_loadField.
  wp_apply (wp_Participant__PrepareDecrease with "[$His_part2 $Htxn2]").
  iIntros (prepared2) "Hprep2".
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

    iDestruct "Hprep1" as "[Hprep1 Htxn1']".
    iDestruct "Htxn1'" as (?) "#Htxn1'".
    iDestruct "Hprep2" as "[Hprep2 Htxn2']".
    iDestruct "Htxn2'" as (?) "#Htxn2'".

    (* Start the commit point *)
    iApply fupd_wp.
    iMod (prepared_participant_start_commit with "Htxn1' Hprep1 Hdodec1 Hunstart1") as "[>Hptsto1 Hfupd1]".
    { done. }
    iMod (prepared_participant_start_commit with "Htxn2' Hprep2 Hdodec2 Hunstart2") as "[>Hptsto2 Hfupd2]".
    { done. }

    iMod (fupd_mask_subseteq) as "Hmask_close"; last iMod "Hacc_pre".
    { done. }
    iDestruct "Hacc_pre" as "((Hacc1 & Hacc2) & Hacc_close)".
    iDestruct (ptsto_agree_frac_value with "Hptsto1 Hacc1") as %[-> _].
    iDestruct (ptsto_agree_frac_value with "Hptsto2 Hacc2") as %[-> _].
    iCombine "Hptsto1 Hacc1" as "Hacc1".
    iCombine "Hptsto2 Hacc2" as "Hacc2".
    rewrite Qp_three_quarter_quarter.

    (***************************)
    (* COMMIT POINT *)
    (***************************)
    iMod (map_update _ _ (word.add v1 amount) with "[] Hacc1") as "[_ Hacc1]".
    { admit. } (* map_ctx *)
    iMod (map_update _ _ (word.sub v2 amount) with "[] Hacc2") as "[_ Hacc2]".
    { admit. }

    rewrite -Qp_three_quarter_quarter.
    iDestruct (fractional_split_1 with "Hacc1") as "[Hptsto1 Hacc1]".
    iDestruct (fractional_split_1 with "Hacc2") as "[Hptsto2 Hacc2]".
    rewrite Qp_three_quarter_quarter.
    iMod ("Hacc_close" with "[$Hacc1 $Hacc2]").
    iMod "Hmask_close".

    iMod ("Hfupd1" with "Hptsto1") as "#Hcom1".
    iMod ("Hfupd2" with "Hptsto2") as "#Hcom2".

    iModIntro.
    wp_apply (wp_Participant__Commit with "[$His_part1 $Hcom1]").
    wp_pures.
    wp_loadField.
    wp_apply (wp_Participant__Commit with "[$His_part2 $Hcom2]").
    by iApply "HΦ".
  - (* abort case *)
    iMod (do_abort with "Hdodec1 Hunstart1") as "#Habort1".
    iMod (do_abort with "Hdodec2 Hunstart2") as "#Habort2".
    wp_loadField.
    wp_apply (wp_Participant__Abort with "[$His_part1 $Habort1]").
    wp_loadField.
    wp_apply (wp_Participant__Abort with "[$His_part2 $Habort2]").
    by iApply "HΦ".
Admitted. (* auth_map *)

End tpc_example.
