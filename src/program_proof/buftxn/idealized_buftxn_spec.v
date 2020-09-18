From iris.algebra Require Import numbers.
From Perennial.algebra Require Import auth_map liftable log_heap.

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
  Context `{!heapG Σ}.
  Context `{!buftxnG Σ}.

  Context (N:namespace).

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_durable γ txn_id :=
    (* oof, this leaks all the abstractions *)
    own γ.(buftxn_txn_names).(txn_walnames).(heapspec.wal_heap_durable_lb) (◯ (MaxNat txn_id)).

  Definition txn_system_inv γ: iProp Σ :=
    ∃ (σs: async (gmap addr object)),
      "H◯async" ∷ own γ.(buftxn_txn_names).(txn_crashstates) (◯E (σs: leibnizO (async (gmap addr object)))) ∗
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
    inv N (txn_system_inv γ).

  (* TODO: eventually need a proper name for this; I think of it as "the right
  to use address [a] in a transaction", together with the fact that the current
  disk value is obj *)
  Definition modify_token γ (a: addr) obj: iProp Σ :=
    txn_proof.mapsto_txn γ.(buftxn_txn_names) a obj.

  (* TODO: I think this just connects to γUnified.(crash_states), which is the
  name of an auth log_heap; when maintaining synchrony the ownership is really
  simple since we only fully own the latest and forward value *)
  Definition stable_maps_to γ (a:addr) obj: iProp Σ :=
    ptsto_ro γ.(buftxn_stable_name) a obj.

  (* this is for a single buftxn (transaction) - not persistent, buftxn's are
  not shareable *)
  Definition is_buftxn l γ γtxn d : iProp Σ :=
    ∃ (mT: gmap addr object),
      ⌜dom (gset _) mT = d⌝ ∗
      mspec.is_buftxn l mT γ.(buftxn_txn_names) ∗
      map_ctx γtxn mT
  .

  Definition buftxn_maps_to γtxn (a: addr) obj : iProp Σ :=
    ∃ q, ptsto γtxn a q obj.

  Theorem lift_into_txn E l γ γtxn d a obj :
    is_buftxn l γ γtxn d -∗
    modify_token γ a obj ={E}=∗
    buftxn_maps_to γtxn a obj ∗ is_buftxn l γ γtxn d.
  Proof.
    (* use mspec.lift_into_txn *)
  Admitted.

  Instance modify_token_conflicting γ : Conflicting (modify_token γ).
  Proof.
    rewrite /modify_token.
    iIntros (????) "H1 H2".
    destruct (decide (a0 = a1)); subst; auto.
    iDestruct (mapsto_txn_2 with "H1 H2") as %[].
  Qed.

  Theorem lift_liftable_into_txn E `{!Liftable P}
          l γ γtxn d :
    is_buftxn l γ γtxn d -∗
    P (modify_token γ) ={E}=∗
    P (buftxn_maps_to γtxn) ∗ is_buftxn l γ γtxn d.
  Proof.
    iIntros "Hctx HP".
    iDestruct (liftable (P:=P) with "HP") as (m) "[Hm HP]".
    iSpecialize ("HP" $! (buftxn_maps_to γtxn)).
    iInduction m as [|i x m] "IH" using map_ind.
    - iModIntro.
      setoid_rewrite big_sepM_empty.
      iSplitL "HP"; [ | iFrame ].
      by iApply "HP".
    - iDestruct (big_sepM_insert with "Hm") as "[Hi Hm]"; auto.
      iMod (lift_into_txn with "Hctx Hi") as "[Hi Hctx]".
      iMod ("IH" with "Hctx Hm [Hi HP]") as "[$ $]".
      + iIntros "Hm".
        iApply "HP".
        rewrite big_sepM_insert //.
        iFrame.
      + auto.
  Qed.

  Definition is_object l a obj: iProp Σ :=
    ∃ dirty, is_buf l a
                    {| bufKind := objKind obj;
                       bufData := objData obj;
                       bufDirty := dirty |}.

  Theorem wp_BufTxn__ReadBuf l γ γtxn d (a: addr) (sz: u64) obj :
    bufSz (objKind obj) = int.nat sz →
    {{{ is_buftxn l γ γtxn d ∗ buftxn_maps_to γtxn a obj }}}
      BufTxn__ReadBuf #l (addr2val a) #sz
    {{{ (l:loc), RET #l; is_object l a obj }}}.
  Proof.
  Admitted.

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
  Theorem wp_BufTxn__CommitWait l γ γtxn d E `{!Liftable P} Q :
    {{{ is_buftxn l γ γtxn d ∗ P (buftxn_maps_to γtxn) ∗
        |={⊤,E}=> ∃ P0, ⌜Liftable P0⌝ ∗ (P0 (stable_maps_to γ) ∗ (P (stable_maps_to γ) ={E,⊤}=∗ Q))  }}}
      BufTxn__CommitWait #l #true
    {{{ (n:u64), RET #n; Q }}}.
  Proof.
  Admitted.

End goose_lang.
