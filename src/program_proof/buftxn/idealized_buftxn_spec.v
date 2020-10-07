From Perennial.Helpers Require Import Map.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import auth_map liftable liftable2 log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

(** * A more separation logic-friendly spec for buftxn

    An attempt to sketch out a synchronous spec for buftxn that has no maps,
    only separation logic resources.

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

(* TODO: move these general theorems (which don't reference lifting at all) to
auth_map.v *)
Theorem map_valid_subset `{Countable L} `{!mapG Σ L V} γ q (m0 m: gmap L V) mq :
  map_ctx γ q m -∗
  ([∗ map] a↦v ∈ m0, ptsto γ a mq v) -∗
  ⌜m0 ⊆ m⌝.
Proof.
  iIntros "Hctx Hm0".
  iInduction m0 as [|l v m0] "IH" using map_ind.
  - iPureIntro.
    apply map_empty_subseteq.
  - rewrite big_sepM_insert //.
    iDestruct "Hm0" as "[Hl Hm0]".
    iDestruct ("IH" with "Hctx Hm0") as %Hsubseteq.
    iDestruct (map_valid with "Hctx Hl") as %Hlookup.
    iPureIntro.
    apply map_subseteq_spec => l' v'.
    intros [(-> & ->) | (? & ?)]%lookup_insert_Some; auto.
    eapply map_subseteq_spec; eauto.
Qed.

Theorem map_union_unchanged_domain `{Countable L} {V} (m m': gmap L V) :
  dom (gset _) m' ⊆ dom _ m →
  dom (gset _) (m' ∪ m) = dom _ m.
Proof. set_solver. Qed.

(* like an update from l↦v0 to l↦v, except that we update an entire subset m0 ⊆
m to m' *)
Theorem map_update_map `{Countable0: Countable L} `{!mapG Σ L V} {γ} (m' m0 m: gmap L V) :
  dom (gset _) m' = dom _ m0 →
  map_ctx γ 1 m -∗
  ([∗ map] a↦v ∈ m0, ptsto_mut γ a 1 v) -∗
  |==> map_ctx γ 1 (m' ∪ m) ∗
       [∗ map] a↦v ∈ m', ptsto_mut γ a 1 v.
Proof.
  iIntros (Hdom) "Hctx Hm0".
  iInduction m0 as [|l v m0] "IH" using map_ind forall (m m' Hdom).
  - rewrite dom_empty_L in Hdom; apply dom_empty_inv_L in Hdom as ->.
    rewrite left_id_L big_sepM_empty.
    by iFrame.
  - rewrite big_sepM_insert //.
    iDestruct "Hm0" as "[Hl Hm0]".
    rewrite dom_insert_L in Hdom.
    assert (l ∈ dom (gset L) m') by set_solver.
    apply elem_of_dom in H0 as [v' Hlookup].
    iMod (map_update _ _ v' with "Hctx Hl") as "[Hctx Hl]".
    iSpecialize ("IH" $! (<[l:=v']> m)).
    apply gset.dom_union_inv in Hdom as (m1&m2 & ? & -> & ? & ?); last first.
    { apply disjoint_singleton_l, not_elem_of_dom; auto. }
    iMod ("IH" $! m2 with "[%] Hctx Hm0") as "[Hctx Hm0]"; auto.
    iModIntro.
    assert (m1 = {[l := v']}).
    { apply dom_singleton_inv in H1 as [v'' ->].
      f_equal.
      erewrite lookup_union_Some_l in Hlookup; last first.
      { rewrite lookup_singleton_Some //. }
      congruence. }
    subst.
    rewrite big_sepM_union // big_sepM_singleton.
    iFrame.
    iExactEq "Hctx".
    f_equal.
    rewrite -union_singleton_l_insert.
    rewrite assoc.
    f_equal.
    rewrite map_union_comm //.
Qed.

Lemma map_subset_dom_eq `{Countable0: Countable L} {V} (m m': gmap L V) :
  dom (gset L) m = dom (gset L) m' →
  m' ⊆ m →
  m = m'.
Proof.
  intros Hdom Hsub.
  apply map_eq => l.
  apply option_eq => v.
  split.
  - intros.
    assert (l ∈ dom (gset _) m') as [v' ?]%elem_of_dom.
    { rewrite -Hdom.
      apply elem_of_dom; eauto. }
    rewrite H0.
    eapply map_subseteq_spec in H0; eauto.
    congruence.
  - apply map_subseteq_spec; auto.
Qed.

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

(* an object is the data for a sub-block object, a dynamic bundle of a kind and
data of the appropriate size *)
(* NOTE(tej): not necessarily the best name, because it's so general as to be
meaningless *)
Notation object := {K & bufDataT K}.

Definition objKind (obj: object): bufDataKind := projT1 obj.
Definition objData (obj: object): bufDataT (objKind obj) := projT2 obj.

Class buftxnG Σ :=
  { buftxn_buffer_inG :> mapG Σ addr object;
    buftxn_mspec_buftxnG :> mspec.buftxnG Σ;
  }.

Record buftxn_names {Σ} :=
  { buftxn_txn_names : @txn_names Σ;
    buftxn_async_name : gname;
  }.

Arguments buftxn_names Σ : assert, clear implicits.

Section async.
Context {Σ: gFunctors} {K V: Type} `{Countable0: Countable K}.

Implicit Types (γ:gname).

(* this idea is for this to have two resources:
    - stable values: a gmap from (txn_id,K) pairs to agree V, which gives persistent knowledge
      of persistent values in old transactions
    - ephemeral ownership: a discrete_funUR from txn_id to gmap K V where
      values are exclusive and typical ownership is over transactions ≥i
  *)
Definition async_ctx γ (σs: async (gmap K V)) : iProp Σ.
Admitted.

Global Instance async_ctx_timeless γ σs : Timeless (async_ctx γ σs).
Admitted.

Definition durable_txn_val γ (i:nat) (k: K) (v: V) : iProp Σ.
Admitted.

Global Instance durable_persistent γ i (k:K) (v:V) : Persistent (durable_txn_val γ i k v).
Admitted.

(* ephemeral_val_from owns ephemeral transactions from i onward (including
future transactions); this is what makes it possible to use ephemeral
maps-to facts to append a new gmap with those addresses updated (see
[map_update_predicate] for the kind of thing we should be able to do) *)
Definition ephemeral_val_from γ (i:nat) (k: K) (v: V) : iProp Σ.
Admitted.

(* ephemeral_txn_val owns only a single point in the ephemeral transactions. We
could probably make this persistent by freezing the address whenever this is
generated. *)
Definition ephemeral_txn_val γ (i:nat) (k: K) (v: V) : iProp Σ.
Admitted.

(* exactly like [ephemeral_txn_val] except owning a half-empty range of
transactions [lo, hi) *)
Definition ephemeral_txn_val_range γ (lo hi:nat) (k: K) (v: V): iProp Σ :=
  [∗ list] i ∈ seq lo (hi-lo), ephemeral_txn_val γ i k v.

Theorem ephemeral_txn_val_range_acc γ lo hi k v i :
  (lo ≤ i < hi)%nat →
  ephemeral_txn_val_range γ lo hi k v -∗
  (* does not return the range under the assumption we make these persistent *)
  ephemeral_txn_val γ i k v.
Proof.
  iIntros (Hbound) "Hrange".
  rewrite /ephemeral_txn_val_range.
  assert (seq lo (hi - lo)%nat !! (i - lo)%nat = Some i).
  { apply lookup_seq; lia. }
  iDestruct (big_sepL_lookup with "Hrange") as "$"; eauto.
Qed.

Theorem ephemeral_val_from_in_bounds γ σs i a v :
  async_ctx γ σs -∗
  ephemeral_val_from γ i a v -∗
  (* if equal, only owns the new transactions and no current ones *)
  ⌜i ≤ length (possible σs)⌝%nat.
Proof.
Admitted.

(* TODO: [ephemeral_val_from i] should probably imply that transaction i is
within bounds, otherwise it doesn't give the right to extend; this rule is then
only valid when i' is also in-bounds *)
Theorem ephemeral_val_from_split i' γ i k v :
  (i ≤ i')%nat →
  ephemeral_val_from γ i k v -∗
  ephemeral_txn_val_range γ i i' k v ∗ ephemeral_val_from γ i' k v.
Proof.
Admitted.

Theorem async_update_map m' γ σs m0 txn_id :
  dom (gset _) m' = dom (gset _) m0 →
  async_ctx γ σs -∗
  ([∗ map] a↦v ∈ m0, ephemeral_val_from γ txn_id a v) -∗
  |==> async_ctx γ (async_put (m' ∪ latest σs) σs) ∗
       ([∗ map] a↦v ∈ m', ephemeral_val_from γ txn_id a v).
Proof.
  (* this can probably be proven by adding a copy of latest σs to the end and
  then updating each address in-place (normally it's not possible to change an
  old txn_id, but perhaps that's fine at the logical level? after all,
  ephemeral_val_from txn_id a v is more-or-less mutable if txn_id is lost) *)
Admitted.

Theorem async_ctx_ephemeral_val_from_split γ σs i a v :
  async_ctx γ σs -∗
  ephemeral_val_from γ i a v -∗
  async_ctx γ σs ∗ ephemeral_txn_val_range γ i (length (possible σs)) a v ∗
  ephemeral_val_from γ (length (possible σs)) a v.
Proof.
  iIntros "Hctx Hi+".
  iDestruct (ephemeral_val_from_in_bounds with "Hctx Hi+") as %Hinbounds.
  iDestruct (ephemeral_val_from_split (length (possible σs)) with "Hi+") as "[Hold H+]"; auto.
  iFrame.
Qed.

Theorem async_ctx_ephemeral_val_from_map_split γ σs i m :
  async_ctx γ σs -∗
  big_opM bi_sep (ephemeral_val_from γ i) m -∗
  async_ctx γ σs ∗ big_opM bi_sep (ephemeral_txn_val_range γ i (length (possible σs))) m ∗
  big_opM bi_sep (ephemeral_val_from γ (length (possible σs))) m.
Proof.
  iIntros "Hctx Hm".
  iInduction m as [|a v m] "IH" using map_ind.
  - rewrite !big_sepM_empty.
    iFrame.
  - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; auto.
    iDestruct (async_ctx_ephemeral_val_from_split with "Hctx Hi") as "(Hctx&Hrange&H+)".
    iDestruct ("IH" with "Hctx Hm") as "(Hctx&Hmrange&Hm+)".
    iFrame.
    rewrite !big_sepM_insert //; iFrame.
Qed.

End async.

Section goose_lang.
  Context `{!buftxnG Σ}.

  Context (N:namespace).

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_durable γ txn_id :=
    (* oof, this leaks all the abstractions *)
    own γ.(buftxn_txn_names).(txn_walnames).(heapspec.wal_heap_durable_lb) (◯ (MaxNat txn_id)).


  Definition txn_system_inv γ: iProp Σ :=
    ∃ (σs: async (gmap addr object)),
      "H◯async" ∷ ghost_var γ.(buftxn_txn_names).(txn_crashstates) (1/2) σs ∗
      "H●latest" ∷ async_ctx γ.(buftxn_async_name) σs
  .

  (* this is for the entire txn manager, and relates it to some ghost state *)
  Definition is_txn_system l γ : iProp Σ :=
    "His_txn" ∷ txn_proof.is_txn l γ.(buftxn_txn_names) ∗
    "Htxn_inv" ∷ inv N (txn_system_inv γ).

  (* TODO: eventually need a proper name for this; I think of it as "the right
  to use address [a] in a transaction", together with the fact that the current
  disk value is obj *)
  Definition modify_token γ (a: addr) obj: iProp Σ :=
    txn_proof.mapsto_txn γ.(buftxn_txn_names) a obj.

  (* this is for a single buftxn (transaction) - not persistent, buftxn's are
  not shareable *)
  Definition is_buftxn l γ γtxn (d: gset addr) : iProp Σ :=
    ∃ (mT: gmap addr object),
      "%Hdom" ∷ ⌜dom (gset _) mT = d⌝ ∗
      "#Htxn_system" ∷ is_txn_system l γ ∗
      "Hbuftxn" ∷ mspec.is_buftxn l mT γ.(buftxn_txn_names) ∗
      "Htxn_ctx" ∷ map_ctx γtxn 1 mT
  .

  Definition buftxn_maps_to γtxn (a: addr) obj : iProp Σ :=
     ptsto_mut γtxn a 1 obj.

  Theorem lift_into_txn E l γ γtxn d a obj :
    ↑invN ⊆ E →
    is_buftxn l γ γtxn d -∗
    modify_token γ a obj ={E}=∗
    (buftxn_maps_to γtxn a obj ∗ is_buftxn l γ γtxn ({[a]} ∪ d)).
  Proof.
    iIntros (?) "Hctx Ha".
    iNamed "Hctx".
    iMod (mspec.BufTxn_lift_one _ _ _ _ _ E with "[$Ha $Hbuftxn]") as "Hupd"; auto.
  Admitted.

  Instance modify_token_conflicting γ : Conflicting (modify_token γ).
  Proof.
    rewrite /modify_token.
    iIntros (????) "H1 H2".
    destruct (decide (a0 = a1)); subst; auto.
    iDestruct (mapsto_txn_2 with "H1 H2") as %[].
  Qed.

  (* TODO: can only lift HoldsAt P d', and new buftxn has domain d ∪ d' *)
  (*
  Theorem lift_liftable_into_txn E `{!Liftable P}
          l γ γtxn d :
    ↑invN ⊆ E →
    is_buftxn l γ γtxn d -∗
    P (modify_token γ) ={E}=∗
    P (buftxn_maps_to γtxn) ∗ is_buftxn l γ γtxn d.
  Proof.
    iIntros (?) "Hctx HP".
    iDestruct (liftable (P:=P) with "HP") as (m) "[Hm HP]".
    iSpecialize ("HP" $! (buftxn_maps_to γtxn)).
    iInduction m as [|i x m] "IH" using map_ind.
    - iModIntro.
      setoid_rewrite big_sepM_empty.
      iSplitL "HP"; [ | iFrame ].
      by iApply "HP".
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; auto.
      iMod (lift_into_txn with "Hctx Hi") as "[Hi Hctx]"; auto.
      iMod ("IH" with "Hctx Hm [Hi HP]") as "[$ $]".
      + iIntros "Hm".
        iApply "HP".
        rewrite big_sepM_insert //.
        iFrame.
      + auto.
  Qed.
*)

  Definition is_object l a obj: iProp Σ :=
    ∃ dirty, is_buf l a
                    {| bufKind := objKind obj;
                       bufData := objData obj;
                       bufDirty := dirty |}.

  Theorem wp_BufTxn__ReadBuf l γ γtxn d (a: addr) (sz: u64) obj :
    bufSz (objKind obj) = int.nat sz →
    {{{ is_buftxn l γ γtxn d ∗ buftxn_maps_to γtxn a obj }}}
      BufTxn__ReadBuf #l (addr2val a) #sz
    {{{ dirty (bufptr:loc), RET #bufptr;
        is_buf bufptr a (Build_buf _ (objData obj) dirty) ∗
        (∀ (obj': bufDataT (objKind obj)) dirty',
            ⌜dirty' = true ∨ (dirty' = dirty ∧ obj' = objData obj)⌝ ∗
            is_buf bufptr a (Build_buf _ obj' dirty') ==∗
            is_buftxn l γ γtxn d ∗ buftxn_maps_to γtxn a (existT (objKind obj) obj')) }}}.
  Proof.
    iIntros (? Φ) "Hpre HΦ".
    iDestruct "Hpre" as "[Hbuftxn Ha]".
    iNamed "Hbuftxn".
    iDestruct (map_valid with "Htxn_ctx Ha") as %Hmt_lookup.
    wp_apply (mspec.wp_BufTxn__ReadBuf with "[$Hbuftxn]").
    { iPureIntro.
      split; first by eauto.
      rewrite H.
      word. }
    iIntros (??) "[Hbuf Hbuf_upd]".
    iApply "HΦ".
    iFrame "Hbuf".
    iIntros (obj' dirty') "[%Hdirty' Hbuf]".
    iMod ("Hbuf_upd" with "[$Hbuf]") as "Hbuftxn".
    { iPureIntro; intuition auto. }
    intuition subst.
    - (* user inserted a new value into the read buffer; need to do the updates
      to incorporate that write *)
      iMod (map_update with "Htxn_ctx Ha") as
          "[Htxn_ctx $]".
      iModIntro.
      iExists (<[a:=existT _ obj']> mT).
      iSplitR.
      { iPureIntro.
        apply elem_of_dom_2 in Hmt_lookup.
        set_solver. }
      iFrame "∗#".
    - (* user did not change buf, so no basic updates are needed *)
      iModIntro.
      change (projT1 obj) with (objKind obj).
      assert (existT (objKind obj) (objData obj) = obj)
        as Hobjeq by (destruct obj; auto).
      rewrite Hobjeq.
      iSplitR "Ha".
      + iExists mT.
        iSplit; first by auto.
        iFrame "Htxn_system Htxn_ctx".
        iExactEq "Hbuftxn".
        rewrite /named.
        f_equal.
        rewrite insert_id //.
      + iExact "Ha".
  Qed.

  (* TODO: state that [data] (a slice of bytes in the implementation) encodes
  the dynamically-typed object [obj], as *)
  Definition data_has_obj (data: list byte) obj : Prop :=
    match objData obj with
    | bufBit _ => False (* TODO *)
    | bufInode _ => False (* TODO *)
    | bufBlock b => vec_to_list b = data
    end.

  Theorem wp_BufTxn__OverWrite l γ γtxn d (a: addr) (sz: u64)
          (data_s: Slice.t) q (data: list byte) obj0 obj :
    bufSz (objKind obj) = int.nat sz →
    data_has_obj data obj →
    {{{ is_buftxn l γ γtxn d ∗ buftxn_maps_to γtxn a obj0 ∗ is_slice data_s byteT q data }}}
      BufTxn__OverWrite #l (addr2val a) (slice_val data_s)
    {{{ RET #(); buftxn_maps_to γtxn a obj }}}.
  Proof.
  Admitted.

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

  (* the idea is that the caller gets to open an invariant and extract an old
  version of whatever they've modified, then substitute it for a newly-prepared
  transaction *)
  (* eventually we need to correlate the footprints of these lifted
  predicates; TODO: won't it be difficult to establish that the footprint of P
  hasn't changed in the invariant? it hasn't because we've had it locked, but we
  don't have ownership over it... *)
  Theorem wp_BufTxn__CommitWait {l γ γtxn} P0 P d txn_id0 :
    N ## invariant.walN →
    N ## invN →
    {{{ "Hbuftxn" ∷ is_buftxn l γ γtxn d ∗
        "HP0" ∷ HoldsAt P0 (ephemeral_val_from (V:=object) γ.(buftxn_async_name) txn_id0) d ∗
        "HP" ∷ HoldsAt P (buftxn_maps_to γtxn) d
    }}}
      BufTxn__CommitWait #l #true
    {{{ (txn_id':nat) (ok:bool), RET #ok;
        if ok then P (λ a v, modify_token γ a v ∗
                             ephemeral_val_from γ.(buftxn_async_name) txn_id' a v) ∗
                     txn_durable γ txn_id'
        else P0 (λ a v, modify_token γ a v ∗ ephemeral_val_from γ.(buftxn_async_name) txn_id' a v)}}}.
  (* crash condition will be [∃ txn_id', P0 (ephemeral_val_from
     γ.(buftxn_async_name) txn_id') ∨ P (ephemeral_val_from γ.(buftxn_async_name)
     txn_id') ]

     where txn_id' is either the original and we get P0 or we commit and advance
     to produce new [ephemeral_val_from]'s *)
  Proof.
    iIntros (?? Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hbuftxn".
    iDestruct (holds_at_map_ctx with "Htxn_ctx HP") as "(Htxn_ctx & Htxn_m & HP)"; first by auto.
    iDestruct (HoldsAt_unfold with "HP0") as (m0) "(%Hdom_m0&Hstable&HP0)".
    wp_apply (mspec.wp_BufTxn__CommitWait _ _ _ _ _
              (λ txn_id', ([∗ map] a↦v∈mT, ephemeral_val_from γ.(buftxn_async_name) (S txn_id') a v))%I
                with "[$Hbuftxn Hstable]").
    { iNamed "Htxn_system".
      iInv "Htxn_inv" as ">Hinner" "Hclo".
      iModIntro.
      iNamed "Hinner".
      iExists σs.
      iFrame "H◯async".
      iIntros "H◯async".

      iMod (async_update_map mT with "H●latest Hstable") as "[H●latest Hstable]".
      { congruence. }

      (* NOTE: we don't use this theorem and instead inline its proof (to some
      extent) since we really need to know what the new map is, to restore
      txn_system_inv. *)
      (* iMod (map_update_predicate with "H●latest HP0 HP") as (m') "[H●latest HP]". *)
      iDestruct (async_ctx_ephemeral_val_from_map_split with "H●latest Hstable")
        as "(H●latest & Hstable_old & Hnew)".

      iMod ("Hclo" with "[H◯async H●latest]") as "_".
      { iNext.
        iExists _.
        iFrame. }
      iModIntro.
      rewrite length_possible_async_put.
      iFrame. }
    iIntros (ok) "Hpost".
    destruct ok.
    - iDestruct "Hpost" as (txn_id) "(HQ&Hlower_bound&Hmod_tokens)".
      iApply ("HΦ" $! (S txn_id)).
      iSplitR "Hlower_bound".
      + iApply "HP".
        iApply big_sepM_sep; iFrame.
      + (* TODO: oops, close but not quite: need to split ephemeral_txn_from to
           include the last transaction, so we can use txn_id and not (S
           txn_id). *)
        iSpecialize ("Hlower_bound" with "[% //]").
        admit.
    - iApply "HΦ".
      iApply "HP0".
      (* TODO: oops, buftxn spec promises _some_ modification tokens on failure,
      should promise the same ones as we started with *)
  Admitted.

End goose_lang.
