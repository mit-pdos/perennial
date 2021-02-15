From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
(* From Perennial.program_proof.lockservice Require Import *)
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
}.

Implicit Type γtpc : tpc_names.
Implicit Type γ : participant_names.

Definition prepared γtpc (tid pid:u64) : iProp Σ := (tid, pid)[[γtpc.(prepared_gn)]]↦ro ().

Definition tpc_inv γtpc tid R0 R1 : iProp Σ :=
  (tid [[γtpc.(committed_gn)]]↦ None ∗
   (prepared γtpc tid 0 ∨ R0) ∗
   (prepared γtpc tid 1 ∨ R1)) ∨
  ∃ d, tid [[γtpc.(committed_gn)]]↦ Some d.

Definition tpcN := nroot .@ "tpc".
Definition is_txn (tid:u64) γtpc R0 R1 : iProp Σ := inv tpcN (tpc_inv γtpc tid R0 R1).

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

Definition ps_mu_inv (ps:loc) γ γtpc pid : iProp Σ :=
  ∃ (kvs_ptr txns_ptr lockMap_ptr:loc) (kvsM:gmap u64 u64) (txnsM:gmap u64 TransactionC),
    "Hkvs" ∷ ps ↦[ParticipantServer.S :: "kvs"] #kvs_ptr ∗
    "Htxns" ∷ ps ↦[ParticipantServer.S :: "txns"] #txns_ptr ∗
    "HlockMap_ptr" ∷ ps ↦[ParticipantServer.S :: "lockmap"] #lockMap_ptr ∗
    "HkvsMap" ∷ is_map (kvs_ptr) kvsM ∗
    "HtxnsMap" ∷ is_map (txns_ptr) txnsM ∗
    "Hkvs_ctx" ∷ map_ctx γ.(ps_kvs) 1 kvsM ∗
    "#HlockMap" ∷ is_lockMap lockMap_ptr γ.(ps_ghs) (fin_to_set u64) (λ x, x [[γ.(ps_kvs)]]↦{1/2} (map_get kvsM x).1) ∗
    "Htxnx_prepared" ∷ [∗ map] tid ↦ txn ∈ txnsM, (prepared γtpc tid pid)
.

Definition participantN := nroot .@ "participant".

Definition is_participant (ps:loc) γ γtpc pid : iProp Σ :=
  ∃ (mu:loc),
  "#Hmu" ∷ readonly (ps ↦[ParticipantServer.S :: "mu"] #mu) ∗
  "#Hmu_inv" ∷ is_lock participantN #mu (ps_mu_inv ps γ γtpc pid)
.

(* TODO: One participant shouldn't know the resources that other participants are contributing *)
Lemma wp_PrepareIncrease (ps:loc) tid γ γtpc (key key' amnt:u64) :
  {{{
       is_txn tid γtpc (∃ v:u64, key [[γ.(ps_kvs)]]↦{1/2} v) (∃ v:u64, key' [[γ.(ps_kvs)]]↦{1/2} v) ∗
       is_participant ps γ γtpc 0
  }}}
    ParticipantServer__PrepareIncrease #ps #tid #key #amnt
  {{{
       (a:u64), RET #a; ⌜a ≠ 0⌝ ∨ ⌜a = 0⌝ ∗ prepared γtpc tid 0
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

  (* Get prepared token *)
  iInv "Htxn" as ">Ht" "Htclose".
  iDestruct "Ht" as "[Ht|Ht]".
  {
    iDestruct "Ht" as "(Hundecided & [Hprep | Hptsto2] & Hirrelevant)"; last first.
    {
      iNamed "Hptsto2".
      (* TODO: Need to add token to rule out this case *)
      admit.
    }
    iMod ("Htclose" with "[Hirrelevant Hptsto Hundecided]") as "_".
    {
      iNext.
      iLeft.
      iFrame. iRight.
      iExists _; iFrame.
    }
    iModIntro.
    iRight.
    iFrame. done.
  }
  { (* Impossible case; commit already decided *)
    admit.
  }

Admitted.

End tpc_example.
