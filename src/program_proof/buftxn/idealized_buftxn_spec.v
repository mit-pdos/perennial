From Perennial.algebra Require Import auth_map.
From Perennial.algebra Require Import liftable.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

(* mspec is a shorthand for referring to the old "map-based" spec, since we will
want to use similar names in this spec *)
Module mspec := buftxn.buftxn_proof.

(* an object is the data for a sub-block object, a dynamic bundle of a kind and
data of the appropriate size *)
(* NOTE(tej): not necessarily the best name, because it's so general as to be
meaningless *)
Notation object := {K & bufDataT K}.

Definition objKind (obj: object): bufDataKind := projT1 obj.
Definition objData (obj: object): bufDataT (objKind obj) := projT2 obj.

Class buftxnG Σ :=
  { buftxn_buffer_inG :> mapG Σ addr object; }.

Section goose_lang.
  Context `{!heapG Σ}.
  Context `{!buftxnG Σ}.

  Implicit Types (l: loc) (γtxn: @txn_names Σ) (γ: gname).
  Implicit Types (obj: object).

  (* this is for the entire txn manager, and relates it to some ghost state *)
  Definition is_txn l γtxn : iProp Σ.
  Admitted.

  (* TODO: eventually need a proper name for this; I think of it as "the right
  to use address [a] in a transaction", together with the fact that the current
  disk value is obj *)
  (* this is probably just [mspec.mapsto_txn] *)
  Definition modify_token γtxn (a: addr) obj: iProp Σ.
  Admitted.

  (* TODO: I think this just connects to γUnified.(crash_states), which is the
  name of an auth log_heap; when maintaining synchrony the ownership is really
  simple since we only fully own the latest and forward value *)
  Definition stable_maps_to γtxn (a:addr) obj: iProp Σ.
  Admitted.

  (* TODO: name this better *)
  Definition buftxn_ctx γ (bufs: gmap addr buf) : iProp Σ :=
    ∃ (owned_bufs: gmap addr object),
      (* NOTE: this data is a superset of what's actually in the buftxn; can do
      an update to move ownership of an address into the transaction, which
      makes it available for reading (actually materializing the value) and
      writing (including overwrites without reading) *)
      "%Hown_super" ∷ ⌜(λ bf, existT bf.(bufKind) bf.(bufData)) <$> bufs ⊆ owned_bufs⌝ ∗
      "Howned●" ∷ map_ctx γ owned_bufs.

  (* this is for a single buftxn (transaction) - not persistent, buftxn's are
  not shareable *)
  (* TODO: this is re-deriving mspec.is_buftxn; build directly on top, but
  replace mT argument with a ghost name *)
  Definition is_buftxn l γtxn γ : iProp Σ :=
    ∃ (txn_l: loc) (bufs_l: loc) (bufs: gmap addr buf),
      "txn" ∷ readonly (l ↦[BufTxn.S :: "txn"] #txn_l) ∗
      "bufs" ∷ readonly (l ↦[BufTxn.S :: "bufs"] #bufs_l) ∗
      "Htxn" ∷ is_txn txn_l γtxn ∗
      "Hbufs" ∷ is_bufmap bufs_l bufs ∗
      "Hctx" ∷ buftxn_ctx γ bufs ∗
      "Hold_stable" ∷ ([∗ map] a↦_ ∈ bufs, ∃ obj0, modify_token γtxn a obj0).

  Definition buftxn_maps_to γ (a: addr) obj : iProp Σ :=
    ∃ q, ptsto γ a q obj.

  Theorem lift_into_txn γtxn γ bufs a obj :
    buftxn_ctx γ bufs -∗
    modify_token γtxn a obj ==∗
    buftxn_maps_to γ a obj ∗ buftxn_ctx γ bufs.
  Proof.
    (* TODO: allocate into buftxn_ctx, consume modify_token into
    buftxn_ctx *)
  Admitted.

  Lemma modify_token_conflicting γtxn :
    Conflicting (modify_token γtxn) (modify_token γtxn).
  Proof.
  Admitted.

  Theorem lift_liftable_into_txn `{!Liftable P}
          γtxn γ bufs :
    buftxn_ctx γ bufs -∗
    P (modify_token γtxn) ==∗
    P (buftxn_maps_to γ) ∗ buftxn_ctx γ bufs.
  Proof.
    iIntros "Hctx HP".
    iDestruct (liftable (P:=P) with "HP") as (m) "[Hm HP]".
    { apply modify_token_conflicting. }
    iSpecialize ("HP" $! (buftxn_maps_to γ)).
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

  Theorem wp_BufTxn__ReadBuf l γtxn γ (a: addr) (sz: u64) obj :
    bufSz (objKind obj) = int.nat sz →
    {{{ is_buftxn l γtxn γ ∗ buftxn_maps_to γ a obj }}}
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

  Theorem wp_BufTxn__OverWrite l γtxn γ (a: addr) (sz: u64)
          (data_s: Slice.t) q (data: list byte) obj0 obj :
    bufSz (objKind obj) = int.nat sz →
    data_has_obj data obj →
    {{{ is_buftxn l γtxn γ ∗ buftxn_maps_to γ a obj0 ∗ is_slice data_s byteT q data }}}
      BufTxn__OverWrite #l (addr2val a) (slice_val data_s)
    {{{ RET #(); buftxn_maps_to γ a obj }}}.
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
  Theorem wp_BufTxn__CommitWait l γtxn γ E `{!Liftable P0, !Liftable P} Q :
    {{{ is_buftxn l γtxn γ ∗ P (buftxn_maps_to γ) ∗
        |={⊤,E}=> (P0 (stable_maps_to γtxn) ∗ (P (stable_maps_to γtxn) ={E,⊤}=∗ Q))  }}}
      BufTxn__CommitWait #l #true
    {{{ (n:u64), RET #n; Q }}}.
  Proof.
  Admitted.

End goose_lang.
