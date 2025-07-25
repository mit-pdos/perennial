Import EqNotations.
From Perennial.Helpers Require Import Map.
From Perennial.algebra Require Import auth_map liftable log_heap async.
From Perennial.base_logic Require Import lib.mono_nat lib.ghost_map.

From Goose.github_com.mit_pdos.go_journal Require Import jrnl.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof obj.obj_proof.
From Perennial.program_proof Require jrnl.jrnl_proof.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

(** * A more separation logic-friendly spec for jrnl

Overview of resources used here:

durable_pointsto_own - durable, exclusive
durable_pointsto - durable but missing modify_token
jrnl_maps_to - ephemeral

is_crash_lock (durable_pointsto_own) (durable_pointsto)
on crash: exchange durable_pointsto for durable_pointsto_own

lift: move durable_pointsto_own into transaction and get jrnl_maps_to and durable_pointsto is added to is_jrnl

is_jrnl P = is_jrnl_mem * is_jrnl_durable P

reads and writes need jrnl_maps_to and is_jrnl_mem

is_jrnl_durable P -* P (P is going to be durable_pointsto) (use this to frame out crash condition)

exchange own_last_frag γ for own_last_frag γ' ∗ modify_token γ' (in sep_jrnl layer)
exchange ephemeral_txn_val γ for ephemeral_txn_val γ' if the transaction id was preserved
 *)

(* mspec is a shorthand for referring to the old "map-based" spec, since we will
want to use similar names in this spec *)
Module mspec := jrnl.jrnl_proof.

Notation versioned_object := ({K & (bufDataT K * bufDataT K)%type}).

Definition objKind (obj: object): bufDataKind := projT1 obj.
Definition objData (obj: object): bufDataT (objKind obj) := projT2 obj.

Class jrnlG Σ : Set :=
  { #[global] jrnl_buffer_inG :: mapG Σ addr object;
    #[global] jrnl_mspec_jrnlG :: mspec.jrnlG Σ;
    #[global] jrnl_asyncG :: asyncG Σ addr object;
  }.

Definition jrnlΣ : gFunctors :=
  #[ mapΣ addr object; mspec.jrnlΣ; asyncΣ addr object ].

#[global]
Instance subG_jrnlΣ Σ : subG jrnlΣ Σ → jrnlG Σ.
Proof. solve_inG. Qed.

Record jrnl_names :=
  { jrnl_txn_names : txn_names;
    jrnl_async_name : async_gname;
  }.

Section goose_lang.
  Context `{!jrnlG Σ}.
  Context `{!heapGS Σ}.

  Context (N:namespace).

  Implicit Types (l: loc) (γ: jrnl_names) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_durable γ txn_id :=
    (* oof, this leaks all the abstractions *)
    mono_nat_lb_own γ.(jrnl_txn_names).(txn_walnames).(heapspec.wal_heap_durable_lb) txn_id.


  Definition txn_system_inv γ: iProp Σ :=
    ∃ (σs: async (gmap addr object)),
      "H◯async" ∷ ghost_var γ.(jrnl_txn_names).(txn_crashstates) (3/4) σs ∗
      "H●latest" ∷ async_ctx γ.(jrnl_async_name) 1 σs
  .

  (* modify_token is an obligation from the jrnl_proof, which is how the txn
  invariant keeps track of exclusive ownership over an address. This proof has a
  more sophisticated notion of owning an address coming from the logical setup
  in [async.v], but we still have to track this token to be able to lift
  addresses into a transaction. *)
  Definition modify_token γ (a: addr) : iProp Σ :=
    ∃ obj, obj.invariant.pointsto_txn γ.(jrnl_txn_names) a obj.

  Global Instance modify_token_conflicting γ T :
    Conflicting (λ (l : addr) (_ : T), modify_token γ l).
  Proof.
    iIntros (a0 v0 a1 v1) "H0 H1".
    iDestruct "H0" as (o0) "H0".
    iDestruct "H1" as (o1) "H1".
    iApply (mspec.pointsto_txn_conflicting with "H0 H1").
  Qed.

  (* The basic statement of what is in the logical, committed disk of the
  transaction system.

  Has three components: the value starting from some txn i, a token giving
  exclusive ownership over transactions ≥ i, and a persistent witness that i is
  durable (so we don't crash to before this fact is relevant). The first two are
  grouped into [ephemeral_val_from]. *)
  Definition durable_pointsto γ (a: addr) obj: iProp Σ :=
    ∃ i, ephemeral_val_from γ.(jrnl_async_name) i a obj ∗
         txn_durable γ i.

  Global Instance durable_pointsto_conflicting γ :
    Conflicting (λ a v, durable_pointsto γ a v).
  Proof.
    iIntros (a0 v0 a1 v1) "H0 H1".
    iDestruct "H0" as (o0) "[H0 _]".
    iDestruct "H1" as (o1) "[H1 _]".
    destruct (decide (a0 = a1)); try done; subst.
    iDestruct (ephemeral_val_from_conflict with "H0 H1") as "H". done.
  Qed.

  Definition durable_pointsto_own γ a obj: iProp Σ :=
    modify_token γ a ∗ durable_pointsto γ a obj.

  Global Instance durable_pointsto_own_discretizable γ a obj: Discretizable (durable_pointsto_own γ a obj).
  Proof. apply _. Qed.

  Definition crash_point γ logm crash_txn : iProp Σ :=
    async_ctx γ.(jrnl_async_name) 1 logm ∗
    ⌜(length (possible logm) >= crash_txn + 1)%nat⌝.

  Definition txn_durable_exchanger γ txn_id :=
    heapspec.heapspec_durable_exchanger γ.(jrnl_txn_names).(txn_walnames) txn_id.

  Lemma txn_durable_exchanger_use γ n lb :
    txn_durable_exchanger γ n -∗
    txn_durable γ lb -∗
    ⌜ (lb ≤ n)%nat ⌝.
  Proof. iIntros. iApply (heapspec.heapspec_durable_exchanger_use with "[$] [$]"). Qed.

  Definition token_exchanger (a:addr) crash_txn γ γ' : iProp Σ :=
    (∃ i, async.own_last_frag γ.(jrnl_async_name) a i) ∨
    (async.own_last_frag γ'.(jrnl_async_name) a crash_txn ∗ modify_token γ' a).

  Definition ephemeral_txn_val_exchanger (a:addr) crash_txn γ γ' : iProp Σ :=
    ∃ v, ephemeral_txn_val γ.(jrnl_async_name) crash_txn a v ∗
         ephemeral_txn_val γ'.(jrnl_async_name) crash_txn a v.

  Definition addr_exchangers {A} txn γ γ' (m : gmap addr A) : iProp Σ :=
    ([∗ map] a↦_ ∈ m,
        token_exchanger a txn γ γ' ∗
        ephemeral_txn_val_exchanger a txn γ γ')%I.

  Definition sep_txn_exchanger γ γ' : iProp Σ :=
    ∃ logm crash_txn,
       "Hcrash_point" ∷ crash_point γ logm crash_txn ∗
       "Hdurable_exchanger" ∷ txn_durable_exchanger γ crash_txn ∗
       "#Hcrash_txn_durable" ∷ txn_durable γ' crash_txn ∗
       "Hexchanger" ∷ addr_exchangers crash_txn γ γ' (latest logm)
  .

  (* TODO: note that we don't promise γ'.(jrnl_txn_names).(txn_kinds) =
  γ.(jrnl_txn_names).(txn_kinds), even though txn_cfupd_res has this fact *)
  Definition txn_cinv γ γ' : iProp Σ :=
    (□ (|C={⊤}=> inv N (sep_txn_exchanger γ γ'))) ∗
    ⌜γ.(jrnl_txn_names).(txn_kinds) = γ'.(jrnl_txn_names).(txn_kinds)⌝.

  (* this is for the entire txn manager, and relates it to some ghost state *)

  Definition is_txn_system γ : iProp Σ :=
    "Htxn_inv" ∷ ncinv N (txn_system_inv γ) ∗
    "His_txn" ∷ ncinv invN (is_txn_always γ.(jrnl_txn_names)).

  Definition is_txn_system_full γ γ' : iProp Σ :=
    "His_txn_system" ∷ is_txn_system γ ∗
    "Htxn_cinv" ∷ txn_cinv γ γ'.

  (*
  Lemma init_txn_system {E} l_txn γUnified dinit σs :
    is_txn l_txn γUnified dinit ∗ ghost_var γUnified.(txn_crashstates) (3/4) σs ={E}=∗
    ∃ γ, ⌜γ.(jrnl_txn_names) = γUnified⌝ ∗
         is_txn_system γ.
  Proof.
    iIntros "[#Htxn Hasync]".
    iMod (async_ctx_init σs) as (γasync) "H●async".
    set (γ:={|jrnl_txn_names := γUnified; jrnl_async_name := γasync; |}).
    iExists γ.
    iMod (ncinv_alloc N E (txn_system_inv γ) with "[-]") as "($&Hcfupd)".
    { iNext.
      iExists _; iFrame. }
    iModIntro.
    simpl.
    iSplit; first by auto.
    iNamed "Htxn"; iFrame "#".
  Qed.
   *)


  Definition is_jrnl_mem l γ dinit γtxn γdurable : iProp Σ :=
    ∃ (mT: gmap addr versioned_object) anydirty,
      "#Htxn_system" ∷ is_txn_system γ ∗
      "Hjrnl" ∷ mspec.is_jrnl l mT γ.(jrnl_txn_names) dinit anydirty ∗
      "Htxn_ctx" ∷ map_ctx γtxn 1 (mspec.modified <$> mT) ∗
      "%Hanydirty" ∷ ⌜anydirty=false →
                      mspec.modified <$> mT = mspec.committed <$> mT⌝ ∗
      "Hdurable" ∷ map_ctx γdurable (1/2) (mspec.committed <$> mT)
  .

  (* To make work with 2PL:
     Consider is_jrnl_mem' that has Hdurable removed and adds mT as an explicit parameter.
     Right before commit, we
     convert is_jrnl_mem' .. .. mT ∗ ([∗ map] a ↦ o ∈ mT durable_pointsto a o) into an is_jrnl. *)

  (* Alternative is define is_jrnl_durable' mT which is just Hdurable and then prove that
     from is_jrnl_mem ∗ ([∗ map] a ↦ o ∈ mT, durable_pointsto a o) ∗ is_jrnl_durable' mT
     can be converted into an is_jrnl

    This seems better.
  *)

  Definition is_jrnl_durable γ γdurable (P0 : (_ -> _ -> iProp Σ) -> iProp Σ) : iProp Σ :=
    ∃ committed_mT,
      "Hdurable_frag" ∷ map_ctx γdurable (1/2) committed_mT ∗
      "Hold_vals" ∷ ([∗ map] a↦v ∈ committed_mT,
                     durable_pointsto γ a v) ∗
      "#HrestoreP0" ∷ □ (∀ pointsto,
                         ([∗ map] a↦v ∈ committed_mT,
                          pointsto a v) -∗
                         P0 pointsto)
  .

  Definition is_jrnl l γ dinit γtxn P0 : iProp Σ :=
    ∃ γdurable,
      "Hjrnl_mem" ∷ is_jrnl_mem l γ dinit γtxn γdurable ∗
      "Hjrnl_durable" ∷ is_jrnl_durable γ γdurable P0.

  Global Instance: Params (@is_jrnl) 4 := {}.

  Global Instance is_jrnl_durable_proper γ γdurable :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (is_jrnl_durable γ γdurable).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_jrnl_durable.
    setoid_rewrite Hequiv.
    reflexivity.
  Qed.

  Global Instance is_jrnl_durable_mono γ γdurable :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (is_jrnl_durable γ γdurable).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_jrnl_durable.
    setoid_rewrite Hequiv.
    reflexivity.
  Qed.

  Theorem is_jrnl_durable_wand γ γdurable P1 P2 :
    is_jrnl_durable γ γdurable P1 -∗
    □(∀ pointsto, P1 pointsto -∗ P2 pointsto) -∗
    is_jrnl_durable γ γdurable P2.
  Proof.
    iIntros "Htxn #Hwand".
    iNamed "Htxn".
    iExists _; iFrame "∗#%".
    iIntros (pointsto) "!> Hm".
    iApply "Hwand". iApply "HrestoreP0". iFrame.
  Qed.

  Global Instance is_jrnl_proper l γ dinit γtxn :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (is_jrnl l γ dinit γtxn).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_jrnl.
    setoid_rewrite Hequiv.
    done.
  Qed.

  Global Instance is_jrnl_mono l γ dinit γtxn :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (is_jrnl l γ dinit γtxn).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_jrnl.
    setoid_rewrite Hequiv.
    done.
  Qed.

  Theorem is_jrnl_wand l γ dinit γtxn P1 P2 :
    is_jrnl l γ dinit γtxn P1 -∗
    □(∀ pointsto, P1 pointsto -∗ P2 pointsto) -∗
    is_jrnl l γ dinit γtxn P2.
  Proof.
    iIntros "Htxn #Hwand".
    iNamed "Htxn".
    iDestruct (is_jrnl_durable_wand with "Hjrnl_durable Hwand") as "Hjrnl_durable".
    iExists _; iFrame.
  Qed.

  Theorem is_jrnl_durable_to_old_pred γ γdurable P0 :
    is_jrnl_durable γ γdurable P0 -∗ P0 (durable_pointsto γ).
  Proof.
    iNamed 1.
    iApply "HrestoreP0". iFrame.
  Qed.

  Theorem is_jrnl_to_old_pred' l γ dinit γtxn γdurable committed_mT :
    "Hjrnl_mem" ∷ is_jrnl_mem l γ dinit γtxn γdurable -∗
    "Hdurable_frag" ∷ map_ctx γdurable (1/2) committed_mT -∗
    "Hold_vals" ∷ ([∗ map] a↦v ∈ committed_mT, durable_pointsto γ a v) -∗
    "Hold_vals" ∷ ([∗ map] a↦v ∈ committed_mT, durable_pointsto_own γ a v).
  Proof.
    iIntros "???".
    iNamed.
    iNamed "Hjrnl_mem".
    iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->.
    iApply big_sepM_sep. iFrame.
    iDestruct (mspec.is_jrnl_to_committed_pointsto_txn with "Hjrnl") as "Hmod".
    iApply (big_sepM_mono with "Hmod").
    iIntros (k x Hkx) "H".
    iExists _; iFrame.
  Qed.

  Theorem is_jrnl_to_old_pred l γ dinit γtxn P0 :
    is_jrnl l γ dinit γtxn P0 -∗ P0 (durable_pointsto_own γ).
  Proof.
    iNamed 1.
    iNamed "Hjrnl_durable".
    iApply "HrestoreP0".
    iApply (
      is_jrnl_to_old_pred' with "Hjrnl_mem Hdurable_frag Hold_vals"
    ).
  Qed.

  Definition jrnl_maps_to γtxn (a: addr) obj : iProp Σ :=
     ptsto_mut γtxn a 1 obj.

  (* TODO: prove this instance for ptsto_mut 1 *)
  Global Instance jrnl_maps_to_conflicting γtxn :
    Conflicting (jrnl_maps_to γtxn).
  Proof.
    rewrite /jrnl_maps_to.
    iIntros (????) "Ha1 Ha2".
    destruct (decide (a0 = a1)); subst; auto.
    iDestruct (ptsto_conflict with "Ha1 Ha2") as %[].
  Qed.

  Definition object_to_versioned (obj: object): versioned_object :=
    existT (objKind obj) (objData obj, objData obj).

  Lemma committed_to_versioned obj :
    mspec.committed (object_to_versioned obj) = obj.
  Proof. destruct obj; reflexivity. Qed.

  Lemma modified_to_versioned obj :
    mspec.modified (object_to_versioned obj) = obj.
  Proof. destruct obj; reflexivity. Qed.

  Lemma durable_pointsto_pointsto_txn_agree' E γ a obj1 obj2 k q :
    ↑N ⊆ E →
    ↑invN ⊆ E →
    N ## invN →
    is_txn_system γ -∗
    durable_pointsto γ a obj1 -∗
    pointsto_txn γ.(jrnl_txn_names) a obj2 -∗
    NC q -∗
    |k={E}=> (⌜obj1 = obj2⌝ ∗ durable_pointsto γ a obj1 ∗ pointsto_txn γ.(jrnl_txn_names) a obj2) ∗ NC q.
  Proof.
    iIntros (???) "#Hinv Ha_i Ha HNC".
    iNamed "Hinv".
    iMod (ncinv_acc_k with "His_txn [$]") as "(>Hinner1&HNC&Hclose1)"; first by auto.
    iMod (ncinv_acc_k with "Htxn_inv [$]") as "(>Hinner2&HNC&Hclose2)"; first by set_solver.
    iAssert (⌜obj1 = obj2⌝)%I as %?; last first.
    { iMod ("Hclose2" with "[$] [$]") as "HNC".
      iMod ("Hclose1" with "[$] [$]") as "HNC".
      iFrame. auto. }
    iNamed "Hinner1".
    iClear "Hheapmatch Hcrashheapsmatch Hmetactx".
    iNamed "Hinner2".
    iDestruct (ghost_var_agree with "Hcrashstates [$]") as %->.
    iDestruct (pointsto_txn_cur with "Ha") as "[Ha _]".
    iDestruct "Ha_i" as (i) "[Ha_i _]".
    iDestruct (ephemeral_val_from_agree_latest with "H●latest Ha_i") as %Hlookup_obj.
    iDestruct (ghost_map_lookup with "Hlogheapctx [$]") as %Hlookup_obj0.
    iPureIntro.
    congruence.
  Qed.

  Lemma durable_pointsto_pointsto_txn_agree E γ a obj1 obj2 :
    ↑N ⊆ E →
    ↑invN ⊆ E →
    N ## invN →
    is_txn_system γ -∗
    durable_pointsto γ a obj1 -∗
    pointsto_txn γ.(jrnl_txn_names) a obj2 -∗
    |NC={E}=> ⌜obj1 = obj2⌝ ∗ durable_pointsto γ a obj1 ∗ pointsto_txn γ.(jrnl_txn_names) a obj2.
  Proof.
    iIntros (???) "#Hinv Ha_i Ha".
    rewrite ncfupd_eq /ncfupd_def.
    iIntros. iApply (fupd_level_fupd _ _ _ O).
    iMod (durable_pointsto_pointsto_txn_agree' with "[$] [$] [$] [$]"); auto.
  Qed.

  Theorem is_jrnl_durable_not_in_map γ a obj γdurable P0 committed_mT :
    durable_pointsto γ a obj -∗
    is_jrnl_durable γ γdurable P0 -∗
    map_ctx γdurable (1 / 2) committed_mT -∗
    ⌜committed_mT !! a = None⌝.
  Proof.
    iIntros "Ha Hdur Hctx".
    destruct (committed_mT !! a) eqn:He; try eauto.
    iNamed "Hdur".
    iDestruct (map_ctx_agree with "Hctx Hdurable_frag") as %->.
    iDestruct (big_sepM_lookup with "Hold_vals") as "Ha2"; eauto.
    iDestruct "Ha" as (i) "[Ha _]".
    iDestruct "Ha2" as (i2) "[Ha2 _]".
    iDestruct (ephemeral_val_from_conflict with "Ha Ha2") as "H".
    done.
  Qed.

  Theorem lift_into_txn' E l γ dinit γtxn γdurable committed_mT a obj :
    ↑N ⊆ E →
    ↑invN ⊆ E →
    N ## invN →
    "Hjrnl_mem" ∷ is_jrnl_mem l γ dinit γtxn γdurable -∗
    "Hdurable_frag" ∷ map_ctx γdurable (1/2) committed_mT -∗
    "Hdurable_maps_to" ∷ durable_pointsto_own γ a obj -∗
    |NC={E}=>
    "Hjrnl_maps_to" ∷ jrnl_maps_to γtxn a obj ∗
    "Hjrnl_mem" ∷ is_jrnl_mem l γ dinit γtxn γdurable ∗
    "Hdurable_frag" ∷ map_ctx γdurable (1/2) (<[a:=obj]>committed_mT) ∗
    "Hdurable_maps_to" ∷ durable_pointsto γ a obj ∗
    "%Hnew" ∷ ⌜committed_mT !! a = None⌝.
  Proof.
    iIntros (HN HinvN HNdisj) "? ? [Ha Ha_i]".
    iNamed.
    iNamed "Hjrnl_mem".

    iDestruct "Ha" as (obj0) "Ha".

    iMod (durable_pointsto_pointsto_txn_agree with "[$] Ha_i Ha") as "(%Heq & Ha_i & Ha)";
      [ solve_ndisj.. | subst obj0 ].

    iDestruct (mspec.is_jrnl_not_in_map with "Hjrnl Ha") as %Hnotin.
    assert ((mspec.modified <$> mT) !! a = None).
    { rewrite lookup_fmap Hnotin //. }
    assert ((mspec.committed <$> mT) !! a = None).
    { rewrite lookup_fmap Hnotin //. }
    iMod (mspec.Op_lift_one _ _ _ _ _ _ E with "[$Ha $Hjrnl]") as "Hjrnl"; auto.
    iMod (map_alloc a obj with "Htxn_ctx") as "[Htxn_ctx Ha]"; eauto.

    iDestruct (map_ctx_agree with "Hdurable Hdurable_frag") as %<-.
    iCombine "Hdurable Hdurable_frag" as "Hdurable".
    iMod (map_alloc a obj with "Hdurable") as "[Hdurable _]"; eauto.
    iDestruct "Hdurable" as "[Hdurable Hdurable_frag]".

    iModIntro.
    iFrame "Ha".
    iSplitR "Hdurable_frag Ha_i".
    {
      iExists (<[a:=object_to_versioned obj]> mT), anydirty.
      iFrame "Htxn_system".
      rewrite !fmap_insert committed_to_versioned modified_to_versioned.
      iFrame.
      iPureIntro. destruct anydirty; intuition congruence.
    }
    iFrame "Hdurable_frag".
    iFrame "∗ %".
  Qed.

  Theorem lift_into_txn E l γ dinit γtxn P0 a obj :
    ↑N ⊆ E →
    ↑invN ⊆ E →
    N ## invN →
    is_jrnl l γ dinit γtxn P0 -∗
    durable_pointsto_own γ a obj
    -∗ |NC={E}=>
    jrnl_maps_to γtxn a obj ∗
    is_jrnl l γ dinit γtxn (λ pointsto, pointsto a obj ∗ P0 pointsto).
  Proof.
    iIntros (HN HinvN HNdisj) "Hctx Hnew".
    iNamed "Hctx".
    iNamed "Hjrnl_durable".
    iDestruct (
      lift_into_txn' _ _ _ _ _ _ _ _ _ HN HinvN HNdisj
      with "Hjrnl_mem Hdurable_frag Hnew"
    ) as "> (?&?&?&?&?)".
    iNamed.
    iFrame "Hjrnl_maps_to".
    iExists _.
    iFrame.

    iModIntro.
    iSplit.
    {
      iApply big_sepM_insert; first by assumption.
      iFrame.
    }
    iModIntro.
    iIntros (pointsto) "H".
    iDestruct (big_sepM_insert with "H") as "[Ha H]"; eauto. iFrame.
    iApply "HrestoreP0"; iFrame.
  Qed.

  Theorem lift_map_into_txn' E l γ dinit γtxn γdurable committed_mT m :
    ↑invN ⊆ E →
    ↑N ⊆ E →
    N ## invN →
    "Hjrnl_mem" ∷ is_jrnl_mem l γ dinit γtxn γdurable -∗
    "Hdurable_frag" ∷ map_ctx γdurable (1/2) committed_mT -∗
    "Hm" ∷ ([∗ map] a↦v ∈ m, durable_pointsto_own γ a v)
    -∗ |NC={E}=>
    "Hjrnl_maps_to" ∷ ([∗ map] a↦v ∈ m, jrnl_maps_to γtxn a v) ∗
    "Hjrnl_mem" ∷ is_jrnl_mem l γ dinit γtxn γdurable ∗
    "Hdurable_frag" ∷ map_ctx γdurable (1/2) (m ∪ committed_mT) ∗
    "Hdurable_pointstos" ∷ ([∗ map] a↦v ∈ m, durable_pointsto γ a v) ∗
    "%Hall_new" ∷ ⌜m ##ₘ committed_mT⌝.
  Proof.
    iIntros (???) "???".
    iNamed.
    iInduction m as [|a v m] "IH" using map_ind forall (committed_mT).
    - setoid_rewrite big_sepM_empty.
      rewrite !left_id.
      iModIntro.
      iFrame.
      iPureIntro.
      apply map_disjoint_empty_l.
    - rewrite !big_sepM_insert //.
      iDestruct "Hm" as "[[Ha_mod Ha_dur] Hm]".
      iAssert (durable_pointsto_own γ a v) with "[Ha_mod Ha_dur]" as "Ha".
      { iFrame. }
      iMod (lift_into_txn' with "Hjrnl_mem Hdurable_frag Ha")
        as "(?&?&?&?&?)"; [ solve_ndisj .. | ].
      iNamed.
      iMod ("IH" with "Hjrnl_mem Hdurable_frag Hm") as "(?&?&?&?&?)".
      iNamed.
      iModIntro.
      rewrite -insert_union_r.
      2: assumption.
      rewrite insert_union_l.
      iFrame.
      iPureIntro.
      apply map_disjoint_insert_r in Hall_new.
      apply map_disjoint_insert_l_2; intuition.
  Qed.

  Theorem lift_map_into_txn E l γ dinit γtxn P0 m :
    ↑invN ⊆ E →
    ↑N ⊆ E →
    N ## invN →
    is_jrnl l γ dinit γtxn P0 -∗
    ([∗ map] a↦v ∈ m, durable_pointsto_own γ a v)
    -∗ |NC={E}=>
    ([∗ map] a↦v ∈ m, jrnl_maps_to γtxn a v) ∗
    is_jrnl l γ dinit γtxn (λ pointsto,
      ([∗ map] a↦v ∈ m, pointsto a v) ∗ P0 pointsto
    ).
  Proof.
    iIntros (???) "Hctx Hm".
    iNamed "Hctx".
    iNamed "Hjrnl_durable".
    iMod (lift_map_into_txn' with "Hjrnl_mem Hdurable_frag Hm")
      as "(?&?&?&?&?)"; [ solve_ndisj.. | ].
    iNamed.
    iModIntro.
    iFrame "Hjrnl_maps_to".
    iExists _.
    iFrame "Hjrnl_mem".
    iExists _.
    iFrame "Hdurable_frag".
    iSplit.
    {
      iApply big_sepM_union; first by assumption.
      iFrame.
    }

    iModIntro.
    iIntros (?) "Hpointsto".
    iDestruct (big_sepM_union with "Hpointsto") as "[Hnew Hold]".
    1: assumption.
    iFrame.
    iApply "HrestoreP0".
    iFrame.
  Qed.

  Lemma conflicting_exists {PROP:bi} (A L V : Type) (P : A → L → V → PROP) :
    (∀ x1 x2, ConflictsWith (P x1) (P x2)) →
    Conflicting (λ a v, ∃ x, P x a v)%I.
  Proof.
    intros.
    hnf; intros a1 v1 a2 v2.
    iIntros "H1 H2".
    iDestruct "H1" as (?) "H1".
    iDestruct "H2" as (?) "H2".
    iApply (H with "H1 H2").
  Qed.

  Theorem lift_liftable_into_txn E `{!Liftable P}
          l γ dinit γtxn P0 :
    ↑invN ⊆ E →
    ↑N ⊆ E →
    N ## invN →
    is_jrnl l γ dinit γtxn P0 -∗
    P (λ a v, durable_pointsto_own γ a v)
    -∗ |NC={E}=>
    P (jrnl_maps_to γtxn) ∗
    is_jrnl l γ dinit γtxn
      (λ pointsto,
       P pointsto ∗ P0 pointsto).
  Proof.
    iIntros (???) "Hctx HP".
    iDestruct (liftable_restore_elim with "HP") as (m) "[Hm #HP]".
    iMod (lift_map_into_txn with "Hctx Hm") as "[Hm Hctx]";
      [ solve_ndisj .. | ].
    iModIntro.
    iFrame.
    iSplitR "Hctx".
    - iApply "HP"; iFrame.
    - iApply (is_jrnl_wand with "Hctx").
      iIntros (pointsto) "!> [Hm $]".
      iApply "HP"; auto.
  Qed.

  Lemma exchange_big_sepM_addrs γ γ' (m0 m1 : gmap addr object) crash_txn :
    dom m0 ⊆ dom m1 →
    txn_durable γ' crash_txn -∗
    addr_exchangers crash_txn γ γ' m1 -∗
    ([∗ map] k0↦x ∈ m0, ephemeral_txn_val γ.(jrnl_async_name) crash_txn k0 x ∗
                        (∃ i v, ephemeral_val_from γ.(jrnl_async_name) i k0 v)) -∗
    addr_exchangers crash_txn γ γ' m1 ∗
    [∗ map] k0↦x ∈ m0, durable_pointsto_own γ' k0 x.
  Proof.
    iIntros (Hdom) "#Hdur H1 H2".
    rewrite /addr_exchangers.
    iCombine "Hdur H1" as "H1".
    iDestruct (big_sepM_mono_with_inv with "H1 H2") as "((_&$)&H)"; last iApply "H".
    iIntros (k o Hlookup) "((#Hdur&Hm)&Hephem)".
    assert (is_Some (m1 !! k)) as (v&?).
    { apply elem_of_dom, Hdom, elem_of_dom. eauto. }
    iDestruct (big_sepM_lookup_acc with "Hm") as "(H&Hm)"; first eassumption.
    iDestruct "Hephem" as "(#Hval0&Hephem)".
    iDestruct "Hephem" as (??) "(_&Htok0)".
    iDestruct "H" as "(Htok&#Hval)".
    iDestruct "Hval" as (?) "(Hval1&Hval2)".
    iDestruct (ephemeral_txn_val_agree with "Hval0 Hval1") as %Heq. subst.
    iDestruct "Htok" as "[Hl|(Hr1&Hr2)]".
    { iExFalso. iDestruct "Hl" as (?) "H".
      iApply (own_last_frag_conflict with "[$] [$]"). }
    iSpecialize ("Hm" with "[Htok0]").
    { iSplitL "Htok0".
      - iLeft. eauto.
      - iExists _. iFrame "#". }
    iFrame "∗#".
  Qed.

  Lemma exchange_durable_pointsto γ γ' m :
    ("#Htxn_cinv" ∷ txn_cinv γ γ' ∗
     "Hm" ∷ [∗ map] a↦v ∈ m, durable_pointsto γ a v) -∗
    |C={⊤}=> ([∗ map] a↦v ∈ m, durable_pointsto_own γ' a v).
  Proof.
    iNamed 1.
    iDestruct "Htxn_cinv" as "[#Hinv %kinds]".
    iMod ("Hinv").
    iIntros "HC".
    iInv ("Hinv") as ">H" "Hclo".
    iNamed "H".
    iDestruct "Hcrash_point" as "(Hasync&%Heq)".
    iAssert (⌜dom m ⊆ dom logm.(latest)⌝)%I with "[Hm Hasync]" as "%Hdom2".
    {
      iInduction m as [| i x m] "IH" using map_ind.
      { iPureIntro; set_solver. }
      rewrite big_sepM_insert //.
      iDestruct "Hm" as "(Hval1&Hval)".
      iDestruct ("IH" with "[$] [$]") as %Hdom.
      iDestruct "Hval1" as (?) "((?&?)&?)".
      iDestruct (ephemeral_val_from_agree_latest with "[$] [$]") as %Hlookup.
      iPureIntro. rewrite dom_insert.
      assert (i ∈ dom (logm.(latest))).
      { apply elem_of_dom. eauto. }
      set_solver.
    }

    iAssert ((txn_durable_exchanger γ crash_txn ∗ async_ctx γ.(jrnl_async_name) 1 logm) ∗
              ([∗ map] k0↦x ∈ m, ephemeral_txn_val γ.(jrnl_async_name) crash_txn k0 x
                  ∗ (∃ (i : nat) (v : object), ephemeral_val_from γ.(jrnl_async_name) i k0 v)))%I
            with "[Hasync Hdurable_exchanger Hm]" as "[[Hdurable_exchanger Hasync] Hm]".
    {
      iCombine "Hdurable_exchanger Hasync" as "H".
      iDestruct (big_sepM_mono_with_inv with "H Hm") as "($&H)"; last iApply "H".
      iIntros (? ? Hlookup) "((Hdurable_exchanger&Hasync)&Hm)".
      iDestruct "Hm" as (?) "(?&?)".
      iDestruct (txn_durable_exchanger_use with "[$] [$]") as %Hlb.
      iDestruct (ephemeral_val_from_val with "Hasync [$]") as "#H".
      { exact Hlb. }
      { lia. }
      iFrame "∗#".
    }
    iDestruct (exchange_big_sepM_addrs with "[$] [$] Hm") as "(Hexchanger&Hval)".
    { eauto. }
    iMod ("Hclo" with "[Hexchanger Hdurable_exchanger Hasync]").
    { iNext. iExists _, _. iFrame "∗#". eauto. }
    iModIntro. eauto.
  Qed.

  Lemma exchange_durable_pointsto1 γ γ' a v :
    ("#Htxn_cinv" ∷ txn_cinv γ γ' ∗
     "Hm" ∷ durable_pointsto γ a v) -∗
    |C={⊤}=> durable_pointsto_own γ' a v.
  Proof.
    iIntros "H".
    iMod (exchange_durable_pointsto γ γ' {[ a := v ]} with "[-]").
    { iNamed "H". iFrame "Htxn_cinv". rewrite big_sepM_singleton. eauto. }
    iModIntro. rewrite big_sepM_singleton. eauto.
  Qed.

  Lemma exchange_pointsto_commit γ γ' m0 m txn_id :
    dom m0 ⊆ dom m →
    ("#Htxn_cinv" ∷ txn_cinv γ γ' ∗
    "Hold_vals" ∷ ([∗ map] k↦x ∈ m0,
          ∃ i : nat, txn_durable γ i ∗
                     ephemeral_txn_val_range γ.(jrnl_async_name) i txn_id k x) ∗
    "Hval" ∷ [∗ map] k↦x ∈ m, ephemeral_val_from γ.(jrnl_async_name) txn_id k x) -∗
    |C={⊤}=> ([∗ map] a↦v ∈ m0, durable_pointsto_own γ' a v) ∨
                  ([∗ map] a↦v ∈ m, durable_pointsto_own γ' a v).
  Proof.
    iIntros (Hdom1) "H". iNamed "H".
    iDestruct "Htxn_cinv" as "[#Hinv %kinds]".
    iMod ("Hinv").
    iIntros "HC".
    iInv ("Hinv") as ">H" "Hclo".
    iNamed "H".
    iDestruct "Hcrash_point" as "(Hasync&%Heq)".
    iAssert (⌜dom m ⊆ dom logm.(latest)⌝)%I with "[Hval Hasync]" as "%Hdom2".
    {
      clear Hdom1.
      iInduction m as [| i x m] "IH" using map_ind.
      { iPureIntro; set_solver. }
      rewrite big_sepM_insert //.
      iDestruct "Hval" as "(Hval1&Hval)".
      iDestruct ("IH" with "[$] [$]") as %Hdom.
      iDestruct (ephemeral_val_from_agree_latest with "[$] [$]") as %Hlookup.
      iPureIntro. rewrite dom_insert.
      assert (i ∈ dom (logm.(latest))).
      { apply elem_of_dom. eauto. }
      set_solver.
    }

    destruct (decide (crash_txn < txn_id)).
    - (* We roll back, txn_id is not durable *)
      iAssert (txn_durable_exchanger γ crash_txn ∗
               ([∗ map] k0↦x ∈ m0, ephemeral_txn_val γ.(jrnl_async_name) crash_txn k0 x))%I
        with "[Hold_vals Hdurable_exchanger]" as "(Hdurable_exchanger&#Hold)".
      {
        iDestruct (big_sepM_mono_with_inv with "Hdurable_exchanger Hold_vals") as "($&H)"; last iApply "H".
        iIntros (?? Hlookup) "(Hdurable_exchanger&H)".
        iDestruct "H" as (i) "(Hdurable&Hrange)".
        iDestruct (txn_durable_exchanger_use with "[$] [$]") as %Hlb.
        iFrame. iApply (ephemeral_txn_val_range_acc with "[$]").
        lia.
      }
      iAssert ([∗ map] k0↦_ ∈ m, ∃ txn_id x, ephemeral_val_from γ.(jrnl_async_name) txn_id k0 x)%I
       with "[Hval]" as "Hval".
      { iApply (big_sepM_mono with "Hval"); eauto. }
      iDestruct (big_sepM_dom with "Hval") as "Hval".
      iDestruct (big_sepS_subseteq with "Hval") as "Hval"; eauto.
      iDestruct (big_sepM_dom with "Hval") as "Hval".
      iCombine "Hold Hval" as "Hval".
      iEval (rewrite -big_sepM_sep) in "Hval".
      iDestruct (exchange_big_sepM_addrs with "[$] [$] Hval") as "(Hexchanger&Hval)".
      { etransitivity; last eassumption; eauto. }
      iMod ("Hclo" with "[Hexchanger Hdurable_exchanger Hasync]").
      { iNext. iExists _, _. iFrame "∗#". eauto. }
      iModIntro. eauto.
    - (* We go forward, txn_id is durable *)
      iAssert (async_ctx γ.(jrnl_async_name) 1 logm ∗
                ([∗ map] k0↦x ∈ m, ephemeral_txn_val γ.(jrnl_async_name) crash_txn k0 x
                    ∗ (∃ (i : nat) (v : object), ephemeral_val_from γ.(jrnl_async_name) i k0 v)))%I
              with "[Hasync Hval]" as "[Hasync Hval]".
      {iDestruct (big_sepM_mono_with_inv with "Hasync Hval") as "($&H)"; last iApply "H".
       iIntros (? ? Hlookup) "(Hasync&Hval)".
       iDestruct (ephemeral_val_from_val with "Hasync Hval") as "#H".
       { trans crash_txn; last reflexivity. lia. }
       { lia. }
       iFrame "Hval ∗#".
      }
      iDestruct (exchange_big_sepM_addrs with "[$] [$] Hval") as "(Hexchanger&Hval)".
      { eauto. }
      iMod ("Hclo" with "[Hexchanger Hdurable_exchanger Hasync]").
      { iNext. iExists _, _. iFrame "∗#". eauto. }
      iModIntro. eauto.
  Qed.

End goose_lang.
