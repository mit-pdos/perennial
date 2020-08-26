From Perennial.algebra Require Import auth_map.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.ffi Require Import disk_prelude.

Notation bufDataDyn := {K & bufDataT K}.

Class buftxnG Σ :=
  { buftxn_buffer_inG :> mapG Σ addr bufDataDyn; }.

Section goose_lang.
  Context `{!heapG Σ}.
  Context `{!buftxnG Σ}.

  Implicit Types (l: loc) (γtxn γ: gname).

  (* this is for the entire txn manager, and relates it to some ghost state *)
  Definition is_txn l γtxn : iProp Σ.
  Admitted.

  (* TODO: this is complicated - it needs to assert ownership over a block in
  the transaction system's abstract state (by instantiating the HOCAP P with
  some auth state) but actually only assert ownership over a sub-block *)
  Definition stable_maps_to γtxn (a: addr) (data: bufDataDyn): iProp Σ.
  Admitted.

  (* TODO: name this better *)
  Definition buftxn_ctx γ (bufs: gmap addr buf) : iProp Σ :=
    ∃ (owned_bufs: gmap addr bufDataDyn),
      (* NOTE: this data is a superset of what's actually in the buftxn; can do
      an update to move ownership of an address into the transaction, which
      makes it available for reading (actually materializing the value) and
      writing (including overwrites without reading) *)
      ⌜(λ bf, existT bf.(bufKind) bf.(bufData)) <$> bufs ⊆ owned_bufs⌝ ∗
      map_ctx γ owned_bufs.

  (* this is for a single buftxn (transaction) - not persistent, buftxn's are
  not shareable *)
  Definition is_buftxn l (γtxn γ: gname) : iProp Σ :=
    ∃ (txn_l: loc) (bufs_l: loc) (bufs: gmap addr buf),
      readonly (l ↦[BufTxn.S :: "txn"] #txn_l) ∗
      readonly (l ↦[BufTxn.S :: "bufs"] #bufs_l) ∗
      is_txn txn_l γtxn ∗
      is_bufmap bufs_l bufs ∗
      buftxn_ctx γ bufs.

  Definition buftxn_maps_to γtxn γ (a: addr) (data: bufDataDyn): iProp Σ :=
    ptsto γ a 1 data ∗
    ∃ data0, stable_maps_to γtxn a data0.

  Theorem lift_into_txn γtxn γ bufs a data :
    buftxn_ctx γ bufs ∗ stable_maps_to γtxn a data  ==∗
    buftxn_maps_to γtxn γ a data ∗ buftxn_ctx γ bufs.
  Proof. Admitted.

End goose_lang.
