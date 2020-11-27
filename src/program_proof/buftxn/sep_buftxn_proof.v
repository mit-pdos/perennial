Import EqNotations.
From Perennial.Helpers Require Import Map.
From iris.base_logic.lib Require Import mnat.
From Perennial.algebra Require Import auth_map liftable liftable2 log_heap async.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

(** * A more separation logic-friendly spec for buftxn

    A layer on top of buftxn_proof that hands out separation logic resources for
    stable, committed but ephemeral, and in-transaction logical disk values.

    The overall flow of using the transaction system is to represent an on-disk
    resource (think of it as a disk maps-to for now) as a stable points-to fact
    and an ephemeral, exclusive "modification token", a right to modify that
    address by using a transaction. The stable fact survives a crash by going
    into an invariant, while the modification token is locked.

    Threads can acquire a number of locks to modification tokens, then "lift"
    those tokens into a transaction. These transactions are like mini-disks,
    whose domain includes all the read and written addresses. A transaction is
    represented by *buftxn.BufTxn in the code, which actually contains the
    addresses that have been read/written.

    The calling thread updates a bunch of modification tokens to construct some
    new state for the locked object. Then they commit the entire transaction (by
    calling buftxn.CommitWait). This spec is synchronous, so it only covers
    CommitWait with sync=true, which greatly simplifies the invariant and crash
    behavior. Committing exchanges takes a stable points-to and modification
    token (which might have a new value) for an address and gives back both, but
    with the stable points-to now at the old value. Of course crucially
    CommitWait does this exchange for all of the addresses in the transaction
    simultaneously, in one fancy update, guaranteeing crash atomicity.

    To make this specification more usable we have a notion of "lifting"
    developed in algebra/liftable that defines liftable predicates as those that
    are parameterized by a points-to fact and can be "lifted" from one points-to
    to another. This allows the spec to be used on entire lifted predicates
    rather than explicit sets of points-to facts. For example, we might define
    [inode_rep mapsto addrs metadata] to define how an inode lays out its
    metadata (attributes like length and type) and a set of data addresses on
    disk, using mapsto. Now we can easily specify an inode in its stable or
    modification token form.

    One complication handled pretty simply here is that the transaction system
    doesn't manage disk blocks but variable-sized objects. This is largely
    explained in the a header comment in the buftxn package Go code; essentially
    each disk block has a statically-assigned "kind" and has only objects of
    that kind's size. Following this discpline will be enforced at write time so
    it can be maintained as an invariant by the txn_proof.
 *)

(* mspec is a shorthand for referring to the old "map-based" spec, since we will
want to use similar names in this spec *)
Module mspec := buftxn.buftxn_proof.

(** There are three main ideas to work out here relative to buftxn_proof:

  (1) mspec transactions are indexed by an explicit map, while here we want an
  auth_map and points-to facts, so we can lift a predicate into the transaction
  map.
  (2) The authoritative state in mspec is the entire list of gmaps for the
  entire disk, which we want to talk about using maps-to, per-address resources.
  The asynchronous buftxn spec needs to be more sophisticated to talk about an
  address in a particular version, which uses the log_heap resource, but here
  due to synchrony we can collapse the whole thing to one gmap and everything is
  simple.
  (3) All parts of the spec should work with lifted predicates, especially
  CommitWait. This is what will give us pleasant reasoning akin to
  coarse-grained locking, even though the code also achieves crash atomicity.
*)

(*
Theorem holds_at_map_ctx `{Countable0: Countable L} {V} `{!mapG Σ L V} (P: (L → V → iProp Σ) → iProp Σ)
        γ q mq d m :
  dom _ m = d →
  map_ctx γ q m -∗
  HoldsAt P (λ a v, ptsto γ a mq v) d -∗
  map_ctx γ q m ∗ ([∗ map] a↦v ∈ m, ptsto γ a mq v) ∗
                PredRestore P m.
Proof.
  iIntros (<-) "Hctx HP".
  iDestruct "HP" as (m') "(%Hdom & Hm & Hmapsto2)"; rewrite /named.
  iDestruct (map_valid_subset with "Hctx Hm") as %Hsubset.
  assert (m = m') by eauto using map_subset_dom_eq; subst m'.
  iFrame.
Qed.
*)

Theorem map_update_predicate `{!EqDecision L, !Countable L} {V} `{!mapG Σ L V}
        (P0 P: (L → V → iProp Σ) → iProp Σ) (γ: gname) mapsto2 d m :
  map_ctx γ 1 m -∗
  HoldsAt P0 (λ a v, ptsto_mut γ a 1 v) d -∗
  HoldsAt P mapsto2 d -∗
  |==> ∃ m', map_ctx γ 1 m' ∗ HoldsAt P (λ a v, ptsto_mut γ a 1 v ∗ mapsto2 a v) d.
Proof.
  iIntros "Hctx HP0 HP".
  iDestruct (HoldsAt_elim_big_sepM with "HP0") as (m0) "[%Hdom_m0 Hstable]".
  iDestruct "HP" as (m') "(%Hdom & HPm & HP)"; rewrite /named.
  iMod (map_update_map m' with "Hctx Hstable") as "[Hctx Hstable]".
  { congruence. }
  iModIntro.
  iExists _; iFrame.
  iDestruct (big_sepM_sep with "[$Hstable $HPm]") as "Hm".
  iExists _; iFrame.
  iPureIntro.
  congruence.
Qed.

(* TODO(tej): we don't get these definitions due to not importing the buftxn
proof; should fix that *)
Notation object := ({K & bufDataT K}).
Notation versioned_object := ({K & (bufDataT K * bufDataT K)%type}).

Definition objKind (obj: object): bufDataKind := projT1 obj.
Definition objData (obj: object): bufDataT (objKind obj) := projT2 obj.

Class buftxnG Σ :=
  { buftxn_buffer_inG :> mapG Σ addr object;
    buftxn_mspec_buftxnG :> mspec.buftxnG Σ;
    buftxn_asyncG :> asyncG Σ addr object;
  }.

Record buftxn_names {Σ} :=
  { buftxn_txn_names : @txn_names Σ;
    buftxn_async_name : async_gname;
  }.

Arguments buftxn_names Σ : assert, clear implicits.

Section goose_lang.
  Context `{!buftxnG Σ}.

  Context (N:namespace).

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_durable γ txn_id :=
    (* oof, this leaks all the abstractions *)
    mnat_own_lb γ.(buftxn_txn_names).(txn_walnames).(heapspec.wal_heap_durable_lb) txn_id.


  Definition txn_system_inv γ: iProp Σ :=
    ∃ (σs: async (gmap addr object)),
      "H◯async" ∷ ghost_var γ.(buftxn_txn_names).(txn_crashstates) (3/4) σs ∗
      "H●latest" ∷ async_ctx γ.(buftxn_async_name) σs
  .

  (* this is for the entire txn manager, and relates it to some ghost state *)
  Definition is_txn_system γ : iProp Σ :=
    "Htxn_inv" ∷ inv N (txn_system_inv γ) ∗
    "His_txn" ∷ inv invN (is_txn_always γ.(buftxn_txn_names)).

  Lemma init_txn_system {E} l_txn γUnified dinit σs :
    is_txn l_txn γUnified dinit ∗ ghost_var γUnified.(txn_crashstates) (3/4) σs ={E}=∗
    ∃ γ, ⌜γ.(buftxn_txn_names) = γUnified⌝ ∗
         is_txn_system γ.
  Proof.
    iIntros "[#Htxn Hasync]".
    iMod (async_ctx_init σs) as (γasync) "H●async".
    set (γ:={|buftxn_txn_names := γUnified; buftxn_async_name := γasync; |}).
    iExists γ.
    iMod (inv_alloc N E (txn_system_inv γ) with "[-]") as "$".
    { iNext.
      iExists _; iFrame. }
    iModIntro.
    simpl.
    iSplit; first by auto.
    iNamed "Htxn"; iFrame "#".
  Qed.

  (* modify_token is an obligation from the buftxn_proof, which is how the txn
  invariant keeps track of exclusive ownership over an address. This proof has a
  more sophisticated notion of owning an address coming from the logical setup
  in [async.v], but we still have to track this token to be able to lift
  addresses into a transaction. *)
  Definition modify_token γ (a: addr) : iProp Σ :=
    ∃ obj, txn.invariant.mapsto_txn γ.(buftxn_txn_names) a obj.

  Global Instance modify_token_conflicting γ T :
    Conflicting (λ (l : addr) (_ : T), modify_token γ l).
  Proof.
    iIntros (a0 v0 a1 v1) "H0 H1".
    iDestruct "H0" as (o0) "H0".
    iDestruct "H1" as (o1) "H1".
    iApply (mspec.mapsto_txn_conflicting with "H0 H1").
  Qed.

  (* The basic statement of what is in the logical, committed disk of the
  transaction system.

  Has three components: the value starting from some txn i, a token giving
  exclusive ownership over transactions ≥ i, and a persistent witness that i is
  durable (so we don't crash to before this fact is relevant). The first two are
  grouped into [ephemeral_val_from]. *)
  Definition durable_mapsto γ (a: addr) obj: iProp Σ :=
    ∃ i, ephemeral_val_from γ.(buftxn_async_name) i a obj ∗
         txn_durable γ i.

  Definition durable_mapsto_own γ a obj: iProp Σ :=
    modify_token γ a ∗ durable_mapsto γ a obj.

  Global Instance durable_mapsto_own_discretizable γ a obj: Discretizable (durable_mapsto_own γ a obj).
  Proof. apply _. Qed.

  Definition is_buftxn_mem l γ dinit γtxn γdurable : iProp Σ :=
    ∃ (mT: gmap addr versioned_object) anydirty,
      "#Htxn_system" ∷ is_txn_system γ ∗
      "Hbuftxn" ∷ mspec.is_buftxn l mT γ.(buftxn_txn_names) dinit anydirty ∗
      "Htxn_ctx" ∷ map_ctx γtxn 1 (mspec.modified <$> mT) ∗
      "%Hanydirty" ∷ ⌜anydirty=false →
                      mspec.modified <$> mT = mspec.committed <$> mT⌝ ∗
      "Hdurable" ∷ map_ctx γdurable (1/2) (mspec.committed <$> mT)
  .

  Definition is_buftxn_durable γ γdurable (P0 : (_ -> _ -> iProp Σ) -> iProp Σ) : iProp Σ :=
    ∃ committed_mT,
      "Hdurable_frag" ∷ map_ctx γdurable (1/2) committed_mT ∗
      "Hold_vals" ∷ ([∗ map] a↦v ∈ committed_mT,
                     durable_mapsto γ a v) ∗
      "#HrestoreP0" ∷ □ (∀ mapsto,
                         ([∗ map] a↦v ∈ committed_mT,
                          mapsto a v) -∗
                         P0 mapsto)
  .

  Definition is_buftxn l γ dinit γtxn P0 : iProp Σ :=
    ∃ γdurable,
      "Hbuftxn_mem" ∷ is_buftxn_mem l γ dinit γtxn γdurable ∗
      "Hbuftxn_durable" ∷ is_buftxn_durable γ γdurable P0.

  Global Instance: Params (@is_buftxn) 4 := {}.

  Global Instance is_buftxn_durable_proper γ γdurable :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (is_buftxn_durable γ γdurable).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_buftxn_durable.
    setoid_rewrite Hequiv.
    reflexivity.
  Qed.

  Global Instance is_buftxn_durable_mono γ γdurable :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (is_buftxn_durable γ γdurable).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_buftxn_durable.
    setoid_rewrite Hequiv.
    reflexivity.
  Qed.

  Theorem is_buftxn_durable_wand γ γdurable P1 P2 :
    is_buftxn_durable γ γdurable P1 -∗
    □(∀ mapsto, P1 mapsto -∗ P2 mapsto) -∗
    is_buftxn_durable γ γdurable P2.
  Proof.
    iIntros "Htxn #Hwand".
    iNamed "Htxn".
    iExists _; iFrame "∗#%".
    iIntros (mapsto) "!> Hm".
    iApply "Hwand". iApply "HrestoreP0". iFrame.
  Qed.

  Global Instance is_buftxn_proper l γ dinit γtxn :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (is_buftxn l γ dinit γtxn).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_buftxn.
    setoid_rewrite Hequiv.
    done.
  Qed.

  Global Instance is_buftxn_mono l γ dinit γtxn :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (is_buftxn l γ dinit γtxn).
  Proof.
    intros P1 P2 Hequiv.
    rewrite /is_buftxn.
    setoid_rewrite Hequiv.
    done.
  Qed.

  Theorem is_buftxn_wand l γ dinit γtxn P1 P2 :
    is_buftxn l γ dinit γtxn P1 -∗
    □(∀ mapsto, P1 mapsto -∗ P2 mapsto) -∗
    is_buftxn l γ dinit γtxn P2.
  Proof.
    iIntros "Htxn #Hwand".
    iNamed "Htxn".
    iDestruct (is_buftxn_durable_wand with "Hbuftxn_durable Hwand") as "Hbuftxn_durable".
    iExists _; iFrame.
  Qed.

  Theorem is_buftxn_durable_to_old_pred γ γdurable P0 :
    is_buftxn_durable γ γdurable P0 -∗ P0 (durable_mapsto γ).
  Proof.
    iNamed 1.
    iApply "HrestoreP0". iFrame.
  Qed.

  Theorem is_buftxn_to_old_pred l γ dinit γtxn P0 :
    is_buftxn l γ dinit γtxn P0 -∗ P0 (durable_mapsto_own γ).
  Proof.
    iNamed 1.
    iNamed "Hbuftxn_mem".
    iNamed "Hbuftxn_durable".
    iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->.
    iApply "HrestoreP0".
    iApply big_sepM_sep. iFrame.
    iDestruct (mspec.is_buftxn_to_committed_mapsto_txn with "Hbuftxn") as "Hmod".
    iApply (big_sepM_mono with "Hmod").
    iIntros (k x Hkx) "H".
    iExists _; iFrame.
  Qed.

  Definition buftxn_maps_to γtxn (a: addr) obj : iProp Σ :=
     ptsto_mut γtxn a 1 obj.

  (* TODO: prove this instance for ptsto_mut 1 *)
  Global Instance buftxn_maps_to_conflicting γtxn :
    Conflicting (buftxn_maps_to γtxn).
  Proof.
    rewrite /buftxn_maps_to.
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

  Lemma durable_mapsto_mapsto_txn_agree E γ a obj1 obj2 :
    ↑N ⊆ E →
    ↑invN ⊆ E →
    N ## invN →
    is_txn_system γ -∗
    durable_mapsto γ a obj1 -∗
    mapsto_txn γ.(buftxn_txn_names) a obj2 -∗
    |={E}=> ⌜obj1 = obj2⌝ ∗ durable_mapsto γ a obj1 ∗ mapsto_txn γ.(buftxn_txn_names) a obj2.
  Proof.
    iIntros (???) "#Hinv Ha_i Ha". iNamed "Hinv".
    iInv "His_txn" as ">Hinner1".
    iInv "Htxn_inv" as ">Hinner2".
    iAssert (⌜obj1 = obj2⌝)%I as %?; last first.
    { iFrame. auto. }
    iNamed "Hinner1".
    iClear "Hheapmatch Hcrashheapsmatch Hmetactx".
    iNamed "Hinner2".
    iDestruct (ghost_var_agree with "Hcrashstates [$]") as %->.
    iDestruct (mapsto_txn_cur with "Ha") as "[Ha _]".
    iDestruct "Ha_i" as (i) "[Ha_i _]".
    iDestruct (ephemeral_val_from_agree_latest with "H●latest Ha_i") as %Hlookup_obj.
    iDestruct (log_heap_valid_cur with "Hlogheapctx [$]") as %Hlookup_obj0.
    iPureIntro.
    congruence.
  Qed.

  Theorem is_buftxn_durable_not_in_map γ a obj γdurable P0 committed_mT :
    durable_mapsto γ a obj -∗
    is_buftxn_durable γ γdurable P0 -∗
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

  Theorem lift_into_txn E l γ dinit γtxn P0 a obj :
    ↑N ⊆ E →
    ↑invN ⊆ E →
    N ## invN →
    is_buftxn l γ dinit γtxn P0 -∗
    durable_mapsto_own γ a obj
    ={E}=∗
    buftxn_maps_to γtxn a obj ∗
    is_buftxn l γ dinit γtxn (λ mapsto, mapsto a obj ∗ P0 mapsto).
  Proof.
    iIntros (???) "Hctx [Ha Ha_i]".
    iNamed "Hctx".
    iNamed "Hbuftxn_mem".

    iDestruct "Ha" as (obj0) "Ha".

    iMod (durable_mapsto_mapsto_txn_agree with "[$] Ha_i Ha") as "(%Heq & Ha_i & Ha)";
      [ solve_ndisj.. | subst obj0 ].

    iDestruct (mspec.is_buftxn_not_in_map with "Hbuftxn Ha") as %Hnotin.
    assert ((mspec.modified <$> mT) !! a = None).
    { rewrite lookup_fmap Hnotin //. }
    assert ((mspec.committed <$> mT) !! a = None).
    { rewrite lookup_fmap Hnotin //. }
    iMod (mspec.BufTxn_lift_one _ _ _ _ _ _ E with "[$Ha $Hbuftxn]") as "Hbuftxn"; auto.
    iMod (map_alloc a obj with "Htxn_ctx") as "[Htxn_ctx Ha]"; eauto.

    iNamed "Hbuftxn_durable".
    iDestruct (map_ctx_agree with "Hdurable Hdurable_frag") as %<-.
    iCombine "Hdurable Hdurable_frag" as "Hdurable".
    iMod (map_alloc a obj with "Hdurable") as "[Hdurable _]"; eauto.
    iDestruct "Hdurable" as "[Hdurable Hdurable_frag]".

    iModIntro.
    iFrame "Ha".
    iExists _. iSplitR "Hdurable_frag Hold_vals Ha_i".
    {
      iExists (<[a:=object_to_versioned obj]> mT), anydirty.
      iFrame "Htxn_system".
      rewrite !fmap_insert committed_to_versioned modified_to_versioned.
      iFrame.
      iPureIntro. destruct anydirty; intuition congruence.
    }
    {
      iExists _. iFrame "Hdurable_frag".
      rewrite !big_sepM_insert //. iFrame.
      iModIntro.
      iIntros (mapsto) "H".
      iDestruct (big_sepM_insert with "H") as "[Ha H]"; eauto. iFrame.
      iApply "HrestoreP0"; iFrame.
    }
  Qed.

  Theorem lift_map_into_txn E l γ dinit γtxn P0 m :
    ↑invN ⊆ E →
    ↑N ⊆ E →
    N ## invN →
    is_buftxn l γ dinit γtxn P0 -∗
    ([∗ map] a↦v ∈ m, durable_mapsto_own γ a v) ={E}=∗
    ([∗ map] a↦v ∈ m, buftxn_maps_to γtxn a v) ∗
                      is_buftxn l γ dinit γtxn
                        (λ mapsto,
                         ([∗ map] a↦v ∈ m, mapsto a v) ∗
                         P0 mapsto).
  Proof.
    iIntros (???) "Hctx Hm".
    iInduction m as [|a v m] "IH" using map_ind forall (P0).
    - setoid_rewrite big_sepM_empty.
      rewrite !left_id.
      setoid_rewrite (@left_id _ _ _ _ emp_sep).
      by iFrame.
    - rewrite !big_sepM_insert //.
      iDestruct "Hm" as "[[Ha_mod Ha_dur] Hm]".
      iAssert (durable_mapsto_own γ a v) with "[Ha_mod Ha_dur]" as "Ha".
      { iFrame. }
      iMod (lift_into_txn with "Hctx Ha") as "[Ha Hctx]"; [ solve_ndisj .. | ].
      iMod ("IH" with "Hctx Hm") as "[Hm Hctx]".
      iModIntro.
      iFrame.
      iApply (is_buftxn_mono with "Hctx"); auto.
      iIntros (mapsto) "(H0 & H1 & $)".
      iApply big_sepM_insert; eauto. iFrame.
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
    is_buftxn l γ dinit γtxn P0 -∗
    P (λ a v, durable_mapsto_own γ a v)
    ={E}=∗
    P (buftxn_maps_to γtxn) ∗
    is_buftxn l γ dinit γtxn
      (λ mapsto,
       P mapsto ∗ P0 mapsto).
  Proof.
    iIntros (???) "Hctx HP".
    iDestruct (liftable_restore_elim with "HP") as (m) "[Hm #HP]".
    iMod (lift_map_into_txn with "Hctx Hm") as "[Hm Hctx]";
      [ solve_ndisj .. | ].
    iModIntro.
    iFrame.
    iSplitR "Hctx".
    - iApply "HP"; iFrame.
    - iApply (is_buftxn_wand with "Hctx").
      iIntros (mapsto) "!> [Hm $]".
      iApply "HP"; auto.
  Qed.

  Theorem wp_BufTxn__Begin (l_txn: loc) γ dinit :
    {{{ is_txn l_txn γ.(buftxn_txn_names) dinit ∗ is_txn_system γ }}}
      Begin #l_txn
    {{{ γtxn l, RET #l; is_buftxn l γ dinit γtxn (λ _, emp) }}}.
  Proof.
    iIntros (Φ) "Hpre HΦ".
    iDestruct "Hpre" as "[#His_txn #Htxn_inv]".
    iApply wp_fupd.
    wp_apply (mspec.wp_buftxn_Begin with "His_txn").
    iIntros (l) "Hbuftxn".
    iMod (map_init ∅) as (γtxn) "Hctx".
    iMod (map_init ∅) as (γdurable) "[Hdurable Hdurable_frag]".
    iModIntro.
    iApply "HΦ".
    iExists γdurable. iSplitR "Hdurable_frag".
    {
      iExists ∅, false.
      rewrite !fmap_empty. iFrame "Hctx".
      iFrame "∗#".
      auto with iFrame.
    }
    {
      iExists ∅.
      rewrite !big_sepM_empty.
      iFrame "∗#".
      auto with iFrame.
    }
  Qed.

  Definition is_object l a obj: iProp Σ :=
    ∃ dirty, is_buf l a
                    {| bufKind := objKind obj;
                       bufData := objData obj;
                       bufDirty := dirty |}.

  Theorem wp_BufTxn__ReadBuf l γ dinit γtxn γdurable (a: addr) (sz: u64) obj :
    bufSz (objKind obj) = int.nat sz →
    {{{ is_buftxn_mem l γ dinit γtxn γdurable ∗ buftxn_maps_to γtxn a obj }}}
      BufTxn__ReadBuf #l (addr2val a) #sz
    {{{ dirty (bufptr:loc), RET #bufptr;
        is_buf bufptr a (Build_buf _ (objData obj) dirty) ∗
        (∀ (obj': bufDataT (objKind obj)) dirty',
            is_buf bufptr a (Build_buf _ obj' dirty') -∗
            ⌜dirty' = true ∨ (dirty' = dirty ∧ obj' = objData obj)⌝ ==∗
            is_buftxn_mem l γ dinit γtxn γdurable ∗ buftxn_maps_to γtxn a (existT (objKind obj) obj')) }}}.
  Proof.
    iIntros (? Φ) "Hpre HΦ".
    iDestruct "Hpre" as "[Hbuftxn Ha]".
    iNamed "Hbuftxn".
    iDestruct (map_valid with "Htxn_ctx Ha") as %Hmt_lookup.
    fmap_Some in Hmt_lookup as vo.
    wp_apply (mspec.wp_BufTxn__ReadBuf with "[$Hbuftxn]").
    { iPureIntro.
      split; first by eauto.
      rewrite H.
      word. }
    iIntros (??) "[Hbuf Hbuf_upd]".
    iApply "HΦ".
    iFrame "Hbuf".
    iIntros (obj' dirty') "Hbuf". iIntros (Hdirty).
    iMod ("Hbuf_upd" with "[$Hbuf]") as "Hbuftxn".
    { iPureIntro; intuition auto. }
    intuition subst.
    - (* user inserted a new value into the read buffer; need to do the updates
      to incorporate that write *)
      iMod (map_update with "Htxn_ctx Ha") as
          "[Htxn_ctx $]".
      iModIntro.
      iExists (<[a:=mspec.mkVersioned (objData (mspec.committed vo)) obj']> mT), true.
      iFrame "Htxn_system".
      rewrite !fmap_insert !mspec.committed_mkVersioned !mspec.modified_mkVersioned //.
      change (existT (objKind ?x) (objData ?x)) with x.
      rewrite (insert_id (mspec.committed <$> mT)); last first.
      { rewrite lookup_fmap Hmt_lookup //. }
      rewrite orb_true_r.
      iFrame "#∗".
      iPureIntro; intros; congruence.
    - (* user did not change buf, so no basic updates are needed *)
      iModIntro.
      simpl.
      rewrite insert_id; last first.
      { rewrite Hmt_lookup.
        destruct vo as [K [c m]]; done. }
      iFrame "Ha".
      iExists mT, _.
      iFrameNamed.
      iPureIntro. destruct anydirty; eauto.
  Qed.

  Definition data_has_obj (data: list byte) (a:addr) obj : Prop :=
    match objData obj with
    | bufBit b =>
      ∃ b0, data = [b0] ∧
            get_bit b0 (word.modu (addrOff a) 8) = b
    | bufInode i => vec_to_list i = data
    | bufBlock b => vec_to_list b = data
    end.

  Theorem data_has_obj_to_buf_data s a obj data :
    data_has_obj data a obj →
    is_slice_small s u8T 1 data -∗ is_buf_data s (objData obj) a.
  Proof.
    rewrite /data_has_obj /is_buf_data.
    iIntros (?) "Hs".
    destruct (objData obj); subst.
    - destruct H as (b' & -> & <-).
      iExists b'; iFrame.
      auto.
    - iFrame.
    - iFrame.
  Qed.

  Theorem is_buf_data_has_obj s a obj :
    is_buf_data s (objData obj) a ⊣⊢ ∃ data, is_slice_small s u8T 1 data ∗ ⌜data_has_obj data a obj⌝.
  Proof.
    iSplit; intros.
    - rewrite /data_has_obj /is_buf_data.
      destruct (objData obj); subst; eauto.
      iDestruct 1 as (b') "[Hs %]".
      iExists [b']; iFrame.
      eauto.
    - iDestruct 1 as (data) "[Hs %]".
      iApply (data_has_obj_to_buf_data with "Hs"); auto.
  Qed.

  (* the subst in this lemma is really where the magic is happening *)
  Lemma is_buf_data_rew K s a obj (H: objKind obj = K) :
    is_buf_data s (objData obj) a -∗
    is_buf_data s (rew [bufDataT] H in objData obj) a.
  Proof.
    subst.
    reflexivity.
  Qed.

  Theorem wp_BufTxn__OverWrite l γ dinit γtxn γdurable (a: addr) (sz: u64)
          (data_s: Slice.t) (data: list byte) obj0 obj :
    bufSz (objKind obj) = int.nat sz →
    data_has_obj data a obj →
    objKind obj = objKind obj0 →
    {{{ is_buftxn_mem l γ dinit γtxn γdurable ∗ buftxn_maps_to γtxn a obj0 ∗
        (* NOTE(tej): this has to be a 1 fraction, because the slice is
        incorporated into the buftxn, is handed out in ReadBuf, and should then
        be mutable. *)
        is_slice_small data_s byteT 1 data }}}
      BufTxn__OverWrite #l (addr2val a) #sz (slice_val data_s)
    {{{ RET #(); is_buftxn_mem l γ dinit γtxn γdurable ∗ buftxn_maps_to γtxn a obj }}}.
  Proof.
    iIntros (??? Φ) "Hpre HΦ".
    iDestruct "Hpre" as "(Hbuftxn & Ha & Hdata)".
    iNamed "Hbuftxn".
    iApply wp_fupd.
    iDestruct (map_valid with "Htxn_ctx Ha") as %Hlookup.
    fmap_Some in Hlookup as vo0.
    wp_apply (mspec.wp_BufTxn__OverWrite _ _ _ _ _ _ (mspec.mkVersioned (objData (mspec.committed vo0)) (rew H1 in objData obj)) with "[$Hbuftxn Hdata]").
    { iSplit; eauto.
      iSplitL.
      - iApply data_has_obj_to_buf_data in "Hdata"; eauto.
        simpl.
        iApply (is_buf_data_rew with "Hdata").
      - iPureIntro.
        simpl.
        destruct vo0 as [K0 [c0 m0]]; simpl in *; subst.
        split; [rewrite H; word|done]. }
    iIntros "Hbuftxn".
    iMod (map_update _ _ obj with "Htxn_ctx Ha") as "[Htxn_ctx Ha]".
    iModIntro.
    iApply "HΦ".
    iFrame "Ha".
    iExists _, true; iFrame "Htxn_system Hbuftxn".
    rewrite !fmap_insert !mspec.committed_mkVersioned !mspec.modified_mkVersioned /=.
    rewrite (insert_id (mspec.committed <$> mT)); last first.
    { rewrite lookup_fmap Hlookup //. }
    iFrame "#∗".
    iSplit.
    2: eauto.
    iExactEq "Htxn_ctx".
    rewrite /named.
    f_equal.
    f_equal.
    destruct obj; simpl in *; subst; reflexivity.
  Qed.

  (*
  lift: modify_token ∗ stable_maps_to ==∗ buftxn_maps_to

  is_crash_lock (P (modify_token ∗ stable_maps_to)) (P stable_maps_to)

  durable_lb i
  -∗ exact_txn_id i' (≥ i)

  ephemeral_maps_to (≥i+1) a v ∗ stable_maps_to i a v0 ∗ durable_lb i
  -∗ (ephemeral_maps_to i' a v ∗ stable_maps_to i' a v) ∨


  P (ephemeral_maps_to (≥i+1)) ∗ P0 (stable_maps_to i) ∗ durable_lb i
  -∗

  {P buftxn_maps_to ∧ P0 stable_maps_to}
    CommitWait
  {P (modify_token ∗ stable_maps_to)}
  {P0 stable_maps_to ∨ P stable_maps_to}
*)

  (* TODO: is this too weak with [durable_mapsto]? does it need to be
  [durable_mapsto_own]? *)
  Lemma async_ctx_durable_map_split γ mT σs :
    async_ctx γ.(buftxn_async_name) σs -∗
    ([∗ map] a↦v ∈ mT, durable_mapsto γ a v) -∗
    |==> async_ctx γ.(buftxn_async_name) σs ∗
          (* this complex expression is persistent and guarantees that the value
          after a crash comes from [mT] if we crash to any current transaction
          (that is, to a transaction id [≤ length (possible σs)]) *)
          (([∗ map] k↦x ∈ mT,
                ∃ i, txn_durable γ i ∗
                     ephemeral_txn_val_range γ.(buftxn_async_name)
                        i (length (possible σs)) k x)) ∗
          ([∗ map] k↦x ∈ mT, ephemeral_val_from γ.(buftxn_async_name)
                               (length (possible σs) - 1) k x).
  Proof.
    iIntros "Hctx".
    iInduction mT as [|k x mT] "IH" using map_ind.
    - rewrite !big_sepM_empty.
      by iFrame.
    - rewrite !big_sepM_insert //.
      iIntros "[Hi Hm]".
      iDestruct "Hi" as (i) "[Hi Hi_durable]".
      iMod (async_ctx_ephemeral_val_from_split with "Hctx Hi")
        as "(Hctx&Hrange&H+)".
      iMod ("IH" with "Hctx Hm") as "(Hctx&Hold&Hm)".
      iModIntro.
      iFrame.
      eauto with iFrame.
  Qed.

  Theorem wp_BufTxn__CommitWait {l γ dinit γtxn} P0 P `{!Liftable P} :
    N ## invariant.walN →
    N ## invN →
    {{{ "Hbuftxn" ∷ is_buftxn l γ dinit γtxn P0 ∗
        "HP" ∷ P (buftxn_maps_to γtxn)
    }}}
      BufTxn__CommitWait #l #true
    {{{ (ok:bool), RET #ok;
        if ok then
            P (λ a v, durable_mapsto_own γ a v)
        else P0 (λ a v, durable_mapsto_own γ a v) }}}.
  (* crash condition will be [∃ txn_id', P0 (ephemeral_val_from
     γ.(buftxn_async_name) txn_id') ∨ P (ephemeral_val_from γ.(buftxn_async_name)
     txn_id') ]

     where txn_id' is either the original and we get P0 or we commit and advance
     to produce new [ephemeral_val_from]'s *)
  Proof.
    iIntros (?? Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hbuftxn".
    iNamed "Hbuftxn_mem".
    iNamed "Hbuftxn_durable".
    iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->.
    iDestruct (liftable_restore_elim with "HP") as (m) "[Hstable HPrestore]".
    iDestruct (map_valid_subset with "Htxn_ctx Hstable") as %HmT_sub.
    (* here things are a little tricky because committing doesn't give us
    [durable_mapsto] but just [ephemeral_val_from] *)
    wp_apply (mspec.wp_BufTxn__CommitWait
                (* ([∗ map] a↦v ∈ (mspec.committed <$> mT),
                 ephemeral_val_from γ.(buftxn_async_name) txn_id0 a v) *) _
                _ _ _ _ _ _
              (λ txn_id', ([∗ map] a↦v∈mspec.modified <$> mT, ephemeral_val_from γ.(buftxn_async_name) txn_id' a v))%I
                with "[$Hbuftxn Hold_vals]").
    { iSplit; [ iModIntro; iAccu | ].
      iDestruct "Htxn_system" as "[Hinv _]".
      iInv "Hinv" as ">Hinner" "Hclo".
      iModIntro.
      iNamed "Hinner".
      iExists σs.
      iFrame "H◯async".
      iIntros "H◯async".

      (* NOTE: we don't use this theorem and instead inline its proof (to some
      extent) since we really need to know what the new map is, to restore
      txn_system_inv. *)
      (* iMod (map_update_predicate with "H●latest HP0 HP") as (m') "[H●latest HP]". *)
      iMod (async_ctx_durable_map_split with "H●latest Hold_vals")
        as "(H●latest & #Hold_vals & Hnew)".
      (* Hold_vals is what we should be using in the crash condition *)

      iMod (async_update_map (mspec.modified <$> mT) with "H●latest Hnew") as "[H●latest Hnew]".
      { set_solver. }

      iMod ("Hclo" with "[H◯async H●latest]") as "_".
      { iNext.
        iExists _.
        iFrame. }
      iModIntro.
      rewrite length_possible_async_put.
      iExactEq "Hnew".
      auto with f_equal lia. }
    iIntros (ok) "Hpost".
    destruct ok.
    - iDestruct "Hpost" as "[Hpost | Hpost]".
      + iDestruct "Hpost" as "[%Hanydirty_true Hpost]".
        iDestruct "Hpost" as (txn_id) "(HQ & Hmod_tokens & Hlower_bound)".
        iAssert (txn_durable γ txn_id) as "#Hdurable_txn_id {Hlower_bound}".
        { iApply "Hlower_bound". done. }
        iApply "HΦ".
        iApply "HPrestore".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        rewrite /durable_mapsto.
        iSplitR "HQ".
        (* TODO: factor this out to a lemma *)
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        iApply (big_sepM_impl with "HQ []").
        iIntros "!>" (k x ?) "Hval".
        iExists _; iFrame "∗#".
      + iDestruct "Hpost" as "[%Hanydirty_false Hpost]".
        iDestruct "Hpost" as "(Hpreq & Hmod_tokens)".
        iApply "HΦ".
        iApply "HPrestore".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        iSplitR "Hpreq".
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        rewrite Hanydirty; eauto.
    - iDestruct "Hpost" as "[Heph Hmod_tokens]".
      iApply "HΦ".
      iApply "HrestoreP0".
      iApply big_sepM_sep; iFrame.
      iApply (big_sepM_mono with "Hmod_tokens").
      iIntros (k x Hkx) "H".
      iExists _; iFrame.
  Qed.

  Theorem wpc_BufTxn__CommitWait {l γ dinit γtxn} P0 P `{!Liftable P} klevel :
    N ## invariant.walN →
    N ## invN →
    N ## mspec.wpwpcN ->
    {{{ "Hbuftxn" ∷ is_buftxn l γ dinit γtxn P0 ∗
        "HP" ∷ P (buftxn_maps_to γtxn)
    }}}
      BufTxn__CommitWait #l #true @ S klevel; ⊤
    {{{ (ok:bool), RET #ok;
        if ok then
            P (λ a v, durable_mapsto_own γ a v)
        else P0 (λ a v, durable_mapsto_own γ a v) }}}
    {{{ P0 (durable_mapsto γ) ∨
         P (durable_mapsto γ) }}}.
  Proof.
    iIntros (??? Φ Φc) "Hpre HΦ". iNamed "Hpre".
    iNamed "Hbuftxn".
    iNamed "Hbuftxn_mem".
    iNamed "Hbuftxn_durable".
    iDestruct (map_ctx_agree with "Hdurable_frag Hdurable") as %->.
    iDestruct (liftable_restore_elim with "HP") as (m) "[Hstable #HPrestore]".
    iDestruct (map_valid_subset with "Htxn_ctx Hstable") as %HmT_sub.

    (* here things are a little tricky because committing doesn't give us
    [durable_mapsto] but just [ephemeral_val_from] *)
    wpc_apply (mspec.wpc_BufTxn__CommitWait
                (* ([∗ map] a↦v ∈ (mspec.committed <$> mT),
                 ephemeral_val_from γ.(buftxn_async_name) txn_id0 a v) *) _
                _ _ _ _ _ _
              (λ txn_id', ([∗ map] a↦v∈mspec.modified <$> mT,
                            ephemeral_val_from γ.(buftxn_async_name) txn_id' a v))%I
                with "[$Hbuftxn Hold_vals]").
    { iSplit; [ iModIntro; iAccu | ].
      iDestruct "Htxn_system" as "[Hinv _]".
      iInv "Hinv" as ">Hinner" "Hclo".
      iModIntro.
      iNamed "Hinner".
      iExists σs.
      iFrame "H◯async".
      iIntros "H◯async".

      (* NOTE: we don't use this theorem and instead inline its proof (to some
      extent) since we really need to know what the new map is, to restore
      txn_system_inv. *)
      (* iMod (map_update_predicate with "H●latest HP0 HP") as (m') "[H●latest HP]". *)
      iMod (async_ctx_durable_map_split with "H●latest Hold_vals")
        as "(H●latest & #Hold_vals & Hnew)".
      (* Hold_vals is what we should be using in the crash condition *)

      iMod (async_update_map (mspec.modified <$> mT) with "H●latest Hnew") as "[H●latest Hnew]".
      { set_solver. }

      iMod ("Hclo" with "[H◯async H●latest]") as "_".
      { iNext.
        iExists _.
        iFrame. }
      iModIntro.
      rewrite length_possible_async_put.
      replace (S (length (possible σs)) - 1)%nat with (length (possible σs))%nat by lia.
      iSplit.
      { iModIntro. iModIntro. generalize (length (possible σs)); intros. iAccu. }
      iExactEq "Hnew".
      auto with f_equal lia. }
    iSplit.
    { iDestruct "HΦ" as "[HΦc _]". iModIntro. iModIntro. iIntros "H".
      iApply "HΦc". iDestruct "H" as "[H|H]".
      { iDestruct "H" as (txnid) "H".
        iDestruct (big_sepM_subseteq with "H") as "H"; eauto.
        (* XXX how to decide whether iLeft or iRight?
          depends on what's actually durable on disk. *)
        iRight. iApply "HPrestore".
        admit.
      }
      { iLeft. iApply "HrestoreP0". iFrame. }
    }
    iModIntro.
    iIntros (ok) "Hpost".
    destruct ok.
    - iDestruct "Hpost" as "[Hpost | Hpost]".
      + iDestruct "Hpost" as "[%Hanydirty_true Hpost]".
        iDestruct "Hpost" as (txn_id) "(HQ & Hmod_tokens & Hlower_bound)".
        iAssert (txn_durable γ txn_id) as "#Hdurable_txn_id {Hlower_bound}".
        { iApply "Hlower_bound". done. }
        iApply "HΦ".
        iApply "HPrestore".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        rewrite /durable_mapsto.
        iSplitR "HQ".
        (* TODO: factor this out to a lemma *)
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        iApply (big_sepM_impl with "HQ []").
        iIntros "!>" (k x ?) "Hval".
        iExists _; iFrame "∗#".
      + iDestruct "Hpost" as "[%Hanydirty_false Hpost]".
        iDestruct "Hpost" as "(Hpreq & Hmod_tokens)".
        iApply "HΦ".
        iApply "HPrestore".
        iApply big_sepM_subseteq; eauto.
        iApply big_sepM_sep; iFrame.
        iSplitR "Hpreq".
        { iApply (big_sepM_mono with "Hmod_tokens").
          rewrite /modify_token. eauto. }
        rewrite Hanydirty; eauto.
    - iDestruct "Hpost" as "[Heph Hmod_tokens]".
      iApply "HΦ".
      iApply "HrestoreP0".
      iApply big_sepM_sep; iFrame.
      iApply (big_sepM_mono with "Hmod_tokens").
      iIntros (k x Hkx) "H".
      iExists _; iFrame.
  Admitted.

  Theorem is_buftxn_mem_durable l γ dinit γtxn P0 γdurable :
    is_buftxn_mem l γ dinit γtxn γdurable -∗
    is_buftxn_durable γ γdurable P0 -∗
    is_buftxn l γ dinit γtxn P0.
  Proof.
    iIntros "Hmem Hdurable".
    iExists _. iFrame.
  Qed.

End goose_lang.
