From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgcoord_repr.

Section btcoord_repr.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type BackupTxnCoordinator struct {                                      @*)
  (*@     // Timestamp of the transaction this backup coordinator tries to finalize. @*)
  (*@     ts      uint64                                                      @*)
  (*@     // Ranks of this backup coordinator.                                @*)
  (*@     rank    uint64                                                      @*)
  (*@     // Participant groups.                                              @*)
  (*@     ptgs    []uint64                                                    @*)
  (*@     // Group coordinators, one for each participant group.              @*)
  (*@     gcoords map[uint64]*BackupGroupCoordinator                          @*)
  (*@     // Global prophecy variable (for verification purpose).             @*)
  (*@     proph   primitive.ProphId                                           @*)
  (*@ }                                                                       @*)
  Definition own_backup_tcoord_ts tcoord (ts : nat) : iProp Σ :=
    ∃ (tsW : u64),
      "HtsP"  ∷ tcoord ↦[BackupTxnCoordinator :: "ts"] #tsW ∗
      "%HtsW" ∷ ⌜uint.nat tsW = ts⌝.

  Definition own_backup_tcoord_rank tcoord (rk : nat) : iProp Σ :=
    ∃ (rkW : u64),
      "HrankP" ∷ tcoord ↦[BackupTxnCoordinator :: "rank"] #rkW ∗
      "%HrkW"  ∷ ⌜uint.nat rkW = rk⌝.

  Definition own_backup_tcoord_ptgs tcoord (ptgs : txnptgs) : iProp Σ :=
    ∃ (ptgsS : Slice.t),
      "HptgsS"  ∷ tcoord ↦[BackupTxnCoordinator :: "ptgs"] (to_val ptgsS) ∗
      "#Hptgs"  ∷ is_txnptgs_in_slice ptgsS ptgs.

  Definition own_backup_tcoord_gcoords tcoord (ptgs : txnptgs) rk ts γ : iProp Σ :=
    ∃ (gcoordsP : loc) (gcoords : gmap u64 loc),
      "HgcoordsP"    ∷ tcoord ↦[BackupTxnCoordinator :: "gcoords"] #gcoordsP ∗
      "Hgcoords"     ∷ own_map gcoordsP (DfracOwn 1) gcoords ∗
      "#Hgcoordsabs" ∷ ([∗ map] gid ↦ gcoord ∈ gcoords, is_backup_gcoord gcoord rk ts gid γ) ∗
      "%Hdomgcoords" ∷ ⌜dom gcoords = ptgs⌝.

  Definition own_backup_tcoord (tcoord : loc) (ts : nat) (γ : tulip_names) : iProp Σ :=
    ∃ (rk : nat) (ptgs : txnptgs) (proph : proph_id),
      "Hts"      ∷ own_backup_tcoord_ts tcoord ts ∗
      "Hrank"    ∷ own_backup_tcoord_rank tcoord rk ∗
      "Hptgs"    ∷ own_backup_tcoord_ptgs tcoord ptgs ∗
      "Hgcoords" ∷ own_backup_tcoord_gcoords tcoord ptgs rk ts γ ∗
      "HprophP"  ∷ tcoord ↦[BackupTxnCoordinator :: "proph"] #proph ∗
      "#Hlnrzed" ∷ is_lnrz_tid γ ts ∗
      (* FIXME: weird naming; wrs is hidden. *)
      "#Hwrs"    ∷ safe_backup_txn γ ts ptgs ∗
      "#Hinv"    ∷ know_tulip_inv_with_proph γ proph.

End btcoord_repr.
