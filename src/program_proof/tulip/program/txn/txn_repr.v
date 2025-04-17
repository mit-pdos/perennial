From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.txn Require Import res.
From Perennial.program_proof.tulip.program.gcoord Require Import gcoord_repr.

Section repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type Txn struct {                                                       @*)
  (*@     // Timestamp of this transaction.                                   @*)
  (*@     ts      uint64                                                      @*)
  (*@     // Buffered write set.                                              @*)
  (*@     wrs     map[uint64]map[string]tulip.Value                           @*)
  (*@     // Participant group of this transaction. Initialized in prepare time. @*)
  (*@     ptgs    []uint64                                                    @*)
  (*@     // Group coordinators for performing reads, prepare, abort, and commit. @*)
  (*@     gcoords map[uint64]*gcoord.GroupCoordinator                         @*)
  (*@     // Global prophecy variable (for verification purpose).             @*)
  (*@     proph   primitive.ProphId                                           @*)
  (*@ }                                                                       @*)
  Definition txn_wrs (wrsP : loc) q (wrs : dbmap) : iProp Σ :=
    ∃ (pwrsmP : gmap u64 loc) (pwrsm : gmap u64 dbmap),
      "HpwrsmP"  ∷ own_map wrsP (DfracOwn 1) pwrsmP ∗
      "Hpwrsm"   ∷ ([∗ map] p; m ∈ pwrsmP; pwrsm, own_map p q m) ∗
      "%Hwrsg"   ∷ ⌜map_Forall (λ g m, m = wrs_group g wrs) pwrsm⌝ ∗
      "%Hdomwrs" ∷ ⌜dom pwrsmP = gids_all⌝.

  Definition own_txn_wrs txn q (wrs : dbmap) : iProp Σ :=
    ∃ (wrsP : loc) (wrspP : loc),
      "HwrsP"  ∷ txn ↦[Txn :: "wrs"] #wrsP ∗
      "Hwrs"   ∷ txn_wrs wrsP q wrs ∗
      "HwrspP" ∷ txn ↦[Txn :: "wrsp"] #wrspP ∗
      "Hwrsp"  ∷ own_map wrspP (DfracOwn 1) wrs.

  Definition own_txn_ptgs_empty txn : iProp Σ :=
    ∃ (ptgsS : Slice.t),
      "HptgsS" ∷ txn ↦[Txn :: "ptgs"] (to_val ptgsS).

  Definition own_txn_ptgs_fixed txn (ptgs : txnptgs) : iProp Σ :=
    ∃ (ptgsS : Slice.t) (ptgsL : list u64),
      "HptgsS"  ∷ txn ↦[Txn :: "ptgs"] (to_val ptgsS) ∗
      "#HptgsL" ∷ own_slice_small ptgsS uint64T DfracDiscarded ptgsL ∗
      "%HptgsL" ∷ ⌜list_to_set ptgsL = ptgs⌝ ∗
      "%Hnd"    ∷ ⌜NoDup ptgsL⌝.

  Definition own_txn_ts txn (tid : nat) : iProp Σ :=
    ∃ (tsW : u64),
      "HtsW"     ∷ txn ↦[Txn :: "ts"] #tsW ∗
      "%Htsword" ∷ ⌜uint.nat tsW = tid⌝.

  Definition own_txn_gcoords txn γ : iProp Σ :=
    ∃ (gcoordsP : loc) (gcoords : gmap u64 loc),
      "HgcoordsP"    ∷ txn ↦[Txn :: "gcoords"] #gcoordsP ∗
      "Hgcoords"     ∷ own_map gcoordsP (DfracOwn 1) gcoords ∗
      "#Hgcoordsabs" ∷ ([∗ map] gid ↦ gcoord ∈ gcoords, is_gcoord gcoord gid γ) ∗
      "%Hdomgcoords" ∷ ⌜dom gcoords = gids_all⌝.

  Definition own_txn_sid γ txn : iProp Σ :=
    ∃ (sid : u64),
      "%Hsid_range" ∷ ⌜ uint.Z sid < zN_TXN_SITES ⌝ ∗
      "Hsid_own" ∷ own_sid γ sid ∗
      "HsidP" ∷ txn ↦[Txn :: "sid"] #sid.

  Definition own_txn_internal txn tid γ : iProp Σ :=
    ∃ (proph : proph_id),
      "Hts"      ∷ own_txn_ts txn tid ∗
      "Hsid"     ∷ own_txn_sid γ txn ∗
      "Hwrs"     ∷ own_txn_wrs txn (DfracOwn 1) ∅ ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs_empty txn ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hgentid" ∷ have_gentid γ.

  Definition own_txn_uninit txn γ : iProp Σ :=
    ∃ tid, "Htxn" ∷ own_txn_internal txn tid γ.

  Definition own_txn_init txn tid γ : iProp Σ :=
    "Htxn"  ∷ own_txn_internal txn tid γ ∗
    "%Hvts" ∷ ⌜valid_ts tid⌝.

  Definition own_txn txn tid rds γ τ : iProp Σ :=
    ∃ (proph : proph_id) wrs,
      "Htxn"     ∷ own_txn_ts txn tid ∗
      "Hsid"     ∷ own_txn_sid γ txn ∗
      "Hwrs"     ∷ own_txn_wrs txn (DfracOwn 1) wrs ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs_empty txn ∗
      (* diff from [own_txn_init] *)
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hgentid" ∷ have_gentid γ ∗
      (* diff from [own_txn_init] *)
      "#Hlnrzts" ∷ is_lnrz_tid γ tid ∗
      (* diff from [own_txn_init] *)
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, is_lnrz_hist_at γ key (pred tid) value) ∗
      "%Hdomr"   ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      (* diff from [own_txn_init] *)
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      (* diff from [own_txn_init] *)
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝.

    Definition own_txn_stable txn tid rds wrs γ τ : iProp Σ :=
    ∃ (proph : proph_id),
      "Htxn"     ∷ own_txn_ts txn tid ∗
      "Hsid"     ∷ own_txn_sid γ txn ∗
      (* diff from [own_txn] *)
      "Hwrs"     ∷ own_txn_wrs txn DfracDiscarded wrs ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      "Hptgs"    ∷ own_txn_ptgs_empty txn ∗
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hgentid" ∷ have_gentid γ ∗
      "#Hlnrzts" ∷ is_lnrz_tid γ tid ∗
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, is_lnrz_hist_at γ key (pred tid) value) ∗
      "%Hdomr"   ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      (* diff from [own_txn] and [wrs] is exposed *)
      "#Htxnwrs" ∷ is_txn_wrs γ tid wrs ∗
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝.

  Definition own_txn_prepared txn tid rds wrs γ τ : iProp Σ :=
    ∃ (proph : proph_id),
      "Htxn"     ∷ own_txn_ts txn tid ∗
      "Hsid"     ∷ own_txn_sid γ txn ∗
      "Hwrs"     ∷ own_txn_wrs txn DfracDiscarded wrs ∗
      "Hgcoords" ∷ own_txn_gcoords txn γ ∗
      (* diff from [own_txn_stable] *)
      "Hptgs"    ∷ own_txn_ptgs_fixed txn (ptgroups (dom wrs)) ∗
      "Htxnmap"  ∷ txnmap_auth τ (wrs ∪ rds) ∗
      "HprophP"  ∷ txn ↦[Txn :: "proph"] #proph ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph ∗
      "#Hgentid" ∷ have_gentid γ ∗
      "#Hlnrzts" ∷ is_lnrz_tid γ tid ∗
      "#Hlnrz"   ∷ ([∗ map] key ↦ value ∈ rds, is_lnrz_hist_at γ key (pred tid) value) ∗
      "#Htxnwrs" ∷ is_txn_wrs γ tid wrs ∗
      "%Hdomr"   ∷ ⌜dom rds ⊆ keys_all⌝ ∗
      "%Hincl"   ∷ ⌜dom wrs ⊆ dom rds⌝ ∗
      "%Hvts"    ∷ ⌜valid_ts tid⌝ ∗
      "%Hvwrs"   ∷ ⌜valid_wrs wrs⌝.

End repr.
