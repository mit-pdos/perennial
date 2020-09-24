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

Theorem map_alloc_predicate `{!EqDecision L, !Countable L} {V} `{!mapG Σ L V}
        (P0 P: (L → V → iProp Σ) → iProp Σ) (γ: gname) mapsto2 d m :
  dom (gset _) m = d →
  map_ctx γ m -∗
  HoldsAt P0 (λ a v, ptsto γ a 1 v) d -∗
  (* TODO: what do we want to do with the old mapsto2 facts? *)
  HoldsAt P mapsto2 d -∗
  |==> ∃ m', map_ctx γ m' ∗ HoldsAt P (λ a v, ptsto γ a 1 v ∗ mapsto2 a v) d.
Proof.
  iIntros (<-) "Hctx HP0 HP".
  iDestruct (HoldsAt_elim_big_sepM with "HP0") as (m0) "[%Hdom_m0 Hstable]".
  iInduction m as [|l a m] "IH" using map_ind.
  - rewrite dom_empty_L.
    iModIntro. iExists ∅.
    iFrame. iExists ∅.
    rewrite dom_empty_L. iSplit; first by auto.
    rewrite big_sepM_empty left_id.
    iIntros (?) "_".
    iApply (holds_at_empty_elim with "HP").
  - rewrite dom_insert_L in Hdom_m0.
    apply gset.dom_union_inv in Hdom_m0 as (m1&m2&?&?&?&?); last first.
    { apply disjoint_singleton_l, not_elem_of_dom; auto. }
    apply dom_singleton_inv in H2 as [v ->].
    rewrite H1.
    rewrite big_sepM_union //.
    rewrite big_sepM_singleton.
    iDestruct "Hstable" as "[Hl Hm2]".
    (* this is getting really messy... *)
Abort.

(* TODO: move these general theorems (which don't reference lifting at all) to
auth_map.v *)
Theorem map_valid_subset `{Countable L, V} `{!mapG Σ L V} γ (m0 m: gmap L V) :
  map_ctx γ m -∗
  ([∗ map] a↦v ∈ m0, ptsto γ a 1 v) -∗
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

Theorem map_union_unchanged_domain `{Countable L, V} (m m': gmap L V) :
  dom (gset _) m' ⊆ dom _ m →
  dom (gset _) (m' ∪ m) = dom _ m.
Proof. set_solver. Qed.

(* like an update from l↦v0 to l↦v, except that we update an entire subset m0 ⊆
m to m' *)
Theorem map_update_map `{Countable L, V} `{!mapG Σ L V} γ (m0 m' m: gmap L V) :
  dom (gset _) m' = dom _ m0 →
  map_ctx γ m -∗
  ([∗ map] a↦v ∈ m0, ptsto γ a 1 v) -∗
  |==> map_ctx γ (m' ∪ m) ∗
       [∗ map] a↦v ∈ m', ptsto γ a 1 v.
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
    apply elem_of_dom in H2 as [v' Hlookup].
    iMod (map_update _ _ v' with "Hctx Hl") as "[Hctx Hl]".
    iSpecialize ("IH" $! (<[l:=v']> m)).
    apply gset.dom_union_inv in Hdom as (m1&m2 & ? & -> & ? & ?); last first.
    { apply disjoint_singleton_l, not_elem_of_dom; auto. }
    iMod ("IH" $! m2 with "[%] Hctx Hm0") as "[Hctx Hm0]"; auto.
    iModIntro.
    assert (m1 = {[l := v']}).
    { apply dom_singleton_inv in H3 as [v'' ->].
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
    buftxn_stable_name : gname;
  }.

Arguments buftxn_names Σ : assert, clear implicits.

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
      "H●latest" ∷ map_ctx γ.(buftxn_stable_name) (latest σs) ∗
      (* TODO(tej): don't think this does anything so far, because we don't have
      a spec for how the async heap gets updated on crash. Joe and I thought we
      might have a more complicated structure with generations and then
      versioned heaps, so that on crash no state gets lost, we just move to a
      new generation and invalidate some transactions from the old one. None of
      this has been worked out, though. *)
      "H◯durable" ∷ txn_durable γ (length $ possible σs)
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

  (* TODO: I think this just connects to γUnified.(crash_states), which is the
  name of an auth log_heap; when maintaining synchrony the ownership is really
  simple since we only fully own the latest and forward value *)
  Definition stable_maps_to γ (a:addr) obj: iProp Σ :=
    ptsto γ.(buftxn_stable_name) a 1 obj.

  (* this is for a single buftxn (transaction) - not persistent, buftxn's are
  not shareable *)
  Definition is_buftxn l γ γtxn d : iProp Σ :=
    ∃ (mT: gmap addr object),
      "%Hdom" ∷ ⌜dom (gset _) mT = d⌝ ∗
      "#Htxn_system" ∷ is_txn_system l γ ∗
      "Hbuftxn" ∷ mspec.is_buftxn l mT γ.(buftxn_txn_names) ∗
      "Htxn_ctx" ∷ map_ctx γtxn mT
  .

  Definition buftxn_maps_to γtxn (a: addr) obj : iProp Σ :=
     ptsto_ro γtxn a obj.

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
    {{{ (bufptr:loc), RET #bufptr;
    (* TODO: this spec needs to return a pair of the bufptr and a fupd that
    incorporates the buf back into is_buftxn; the caller can manipulate the buf
    and then return it to the buftxn system *)
        is_buftxn l γ γtxn d }}}.
  Proof.
    iIntros (? Φ) "Hpre HΦ".
    iDestruct "Hpre" as "[Hbuftxn #Ha]".
    iNamed "Hbuftxn".
    iDestruct (map_ro_valid with "Htxn_ctx Ha") as %Hmt_lookup.
    iApply wp_fupd.
    wp_apply (mspec.wp_BufTxn__ReadBuf with "[$Hbuftxn]").
    { iPureIntro.
      split; first by eauto.
      rewrite H.
      word. }
    iIntros (??) "[Hbuf Hbuf_upd]".
    iMod ("Hbuf_upd" $! (projT2 obj) dirty with "[$Hbuf]") as "Hbuftxn".
    { auto. }
    iModIntro.
    iApply "HΦ".
    iExists mT.
    iSplit; first by auto.
    iFrame "#Htxn_ctx".
    iExactEq "Hbuftxn".
    f_equal.
    rewrite insert_id //.
    rewrite Hmt_lookup.
    f_equal.
    destruct obj; auto.
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

  (* TODO: almost certainly wrong in some fundamental way *)
  (* the idea is that the caller gets to open an invariant and extract an old
  version of whatever they've modified, then substitute it for a newly-prepared
  transaction *)
  (* eventually we need to correlate the footprints of these lifted
  predicates; TODO: won't it be difficult to establish that the footprint of P
  hasn't changed in the invariant? it hasn't because we've had it locked, but we
  don't have ownership over it... *)
  Theorem wp_BufTxn__CommitWait {l γ γtxn} E P Q d :
    ↑N ⊆ E →
    {{{ "Hbuftxn" ∷ is_buftxn l γ γtxn d ∗
        "HP" ∷ HoldsAt P (buftxn_maps_to γtxn) d ∗
        "Hfupd" ∷ (|={⊤ ∖ ↑invariant.walN ∖ ↑invN,E}=> ∃ P0, HoldsAt P0 (stable_maps_to γ) d
                    ∗ (P (stable_maps_to γ) ={E,⊤}=∗ Q))  }}}
      BufTxn__CommitWait #l #true
    {{{ (n:u64), RET #n; Q ∗ P (modify_token γ) }}}.
  (* TODO: has a wpc might need a PreQ ∧ on the fupd *)
  Proof.
    iIntros (? Φ) "Hpre HΦ"; iNamed "Hpre".
    iNamed "Hbuftxn".
    wp_apply (mspec.wp_BufTxn__CommitWait with "[$Hbuftxn HP Hfupd]").
    { iMod "Hfupd" as (P0) "[HP0 HQ]".
      iNamed "Htxn_system".
      iInv "Htxn_inv" as ">Hinner" "Hclo".
      iModIntro.
      iNamed "Hinner".
      iExists σs.
      iFrame "H◯async".
      iIntros "Hown◯async'".
      iDestruct (HoldsAt_elim_big_sepM with "HP0") as (m0) "[%Hdom_m0 Hstable]".

      (* TODO: need to allocate a whole predicate P into map_ctx, transforming
      the old resources in Hstable into stable_maps_to over mT; then we can use
      HP to restore P using stable_maps_to *)
      (* TODO: this is probably the time to also construct P (modify_token γ)
      somehow from HP... *)
  Admitted.

End goose_lang.
