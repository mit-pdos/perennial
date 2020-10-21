From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.

From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import deletable_heap log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Class txnG (Σ: gFunctors) :=
  {
    txn_boolG :> ghost_varG Σ bool;
    txn_walheapG :> walheapG Σ;
    txn_logheapG :> log_heapPreG addr {K & bufDataT K} Σ;
    txn_metaheapG :> gen_heapPreG addr gname Σ;
    txn_crashstatesG :> ghost_varG Σ (async (gmap addr {K & bufDataT K}));
  }.

Record txn_names {Σ} := {
  txn_logheap : log_heapG addr {K & bufDataT K} Σ;
  txn_metaheap : gen_heapG addr gname Σ;
  txn_walnames : @wal_heap_gnames Σ;
  txn_crashstates : gname;
  txn_kinds : gmap u64 bufDataKind;
}.

Section goose_lang.
Context `{!txnG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".

Definition mapsto_txn (γ : txn_names) (l : addr) (v : {K & bufDataT K}) : iProp Σ :=
  ∃ γm,
    "Hmapsto_log" ∷ mapsto_cur (hG := γ.(txn_logheap)) l v ∗
    "Hmapsto_meta" ∷ mapsto (hG := γ.(txn_metaheap)) l 1 γm ∗
    "Hmod_frag" ∷ ghost_var γm (1/2) true.

Theorem mapsto_txn_2 γ a v0 v1 :
  mapsto_txn γ a v0 -∗
  mapsto_txn γ a v1 -∗
  False.
Proof.
  rewrite /mapsto_txn.
  iIntros "H0 H1".
  iDestruct "H0" as (g0) "(H0log & H0m & H0own)".
  iDestruct "H1" as (g1) "(H1log & H1m & H1own)".
  iDestruct (mapsto_disjoint with "H0m H1m") as %Hnoteq.
  eauto.
Qed.

Definition bufDataT_in_block (walblock : Block) blockK (blkno off : u64) (bufData : {K & bufDataT K}) : Prop :=
  is_bufData_at_off walblock off (projT2 bufData) ∧
  valid_addr (Build_addr blkno off) ∧
  valid_off (projT1 bufData) off ∧
  blockK = projT1 bufData.

Definition bufDataTs_in_block (installed : Block) (bs : list Block) (blkno : u64) blockK
                              (offmap : gmap u64 {K & bufDataT K})
                              (metamap : gmap u64 gname) : iProp Σ :=
  ( [∗ map] off ↦ bufData;γm ∈ offmap;metamap,
      ∃ (modifiedSinceInstall : bool),
      "%Hoff_in_block" ∷ ⌜ bufDataT_in_block (latest_update installed bs) blockK blkno off bufData ⌝ ∗
      "Hoff_own" ∷ ghost_var γm (1/2) modifiedSinceInstall ∗
      "%Hoff_prefix_in_block" ∷ ⌜ if modifiedSinceInstall then True else
        ∀ prefix,
          bufDataT_in_block (latest_update installed (take prefix bs)) blockK blkno off bufData ⌝
  )%I.

Global Instance bufDataTs_in_block_timeless installed bs blkno blockK offmap metamap :
  Timeless (bufDataTs_in_block installed bs blkno blockK offmap metamap) := _.

Definition bufDataTs_in_crashblock (walblock : Block) (blkno : u64) blockK
                                   (offmap : gmap u64 {K & bufDataT K}) : iProp Σ :=
  (* Very similar to txn_bufDataT_in_block *)
  ( [∗ map] off ↦ bufData ∈ offmap,
      ⌜ bufDataT_in_block walblock blockK blkno off bufData ⌝
  )%I.

Definition is_txn_always (γ : txn_names) : iProp Σ :=
  (
    ∃ (logm : async (gmap addr {K & bufDataT K}))
      (metam : gmap addr gname)
      (crash_heaps : async (gmap u64 Block)),
      "Hlogheapctx" ∷ log_heap_ctx (hG := γ.(txn_logheap)) logm ∗
      "Hcrashstates" ∷ ghost_var γ.(txn_crashstates) (1/2) logm ∗
      "Hmetactx" ∷ gen_heap_ctx (hG := γ.(txn_metaheap)) metam ∗
      "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block (latest logm);gmap_addr_by_block metam,
        ∃ installed bs blockK,
          "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
          "Htxn_hb" ∷ mapsto (hG := γ.(txn_walnames).(wal_heap_h)) blkno 1 (HB installed bs) ∗
          "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
      "Hcrashheaps" ∷ ghost_var γ.(txn_walnames).(wal_heap_crash_heaps) (1/2) crash_heaps ∗
      "Hcrashheapsmatch" ∷ ( [∗ list] logmap;walheap ∈ possible logm;possible crash_heaps,
        [∗ map] blkno ↦ offmap;walblock ∈ gmap_addr_by_block logmap;walheap,
          ∃ blockK,
            "%Htxn_cb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
            "Htxn_in_cb" ∷ bufDataTs_in_crashblock walblock blkno blockK offmap )
  )%I.

Global Instance is_txn_always_timeless γ :
  Timeless (is_txn_always γ) := _.

Definition is_txn_locked l γ : iProp Σ :=
  (
    ∃ (nextId : u64) (pos : u64) lwh,
      "Hwal_latest" ∷ is_locked_walheap γ lwh ∗
      "Histxn_pos" ∷ l ↦[Txn.S :: "pos"] #pos
 )%I.

Definition is_txn (l : loc) (γ : txn_names) dinit : iProp Σ :=
  (
    ∃ (mu : loc) (walptr : loc),
      "Histxn_mu" ∷ readonly (l ↦[Txn.S :: "mu"] #mu) ∗
      "Histxn_wal" ∷ readonly (l ↦[Txn.S :: "log"] #walptr) ∗
      "Hiswal" ∷ is_wal (wal_heap_inv (txn_walnames γ)) walptr (wal_heap_walnames (txn_walnames γ)) dinit ∗
      "Histxna" ∷ inv invN (is_txn_always γ) ∗
      "Histxn_lock" ∷ is_lock lockN #mu (is_txn_locked l (txn_walnames γ))
  )%I.

Global Instance is_txn_persistent l γ dinit : Persistent (is_txn l γ dinit) := _.

Theorem mapsto_txn_valid γ a v E :
  ↑invN ⊆ E ->
  inv invN (is_txn_always γ) -∗
  mapsto_txn γ a v ={E}=∗
    mapsto_txn γ a v ∗ ⌜ valid_addr a ∧ valid_off (projT1 v) a.(addrOff) ∧ γ.(txn_kinds) !! a.(addrBlock) = Some (projT1 v) ⌝.
Proof.
  iIntros (HN) "#Hinv H".
  iNamed "H".
  iInv invN as ">Halways".
  iNamed "Halways".

  iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as "%Hlogvalid".
  iDestruct (gen_heap_valid with "Hmetactx Hmapsto_meta") as "%Hmetavalid".

  eapply gmap_addr_by_block_lookup in Hlogvalid; destruct Hlogvalid.
  eapply gmap_addr_by_block_lookup in Hmetavalid; destruct Hmetavalid.
  intuition idtac.

  iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hblockmatch Hheapmatch]"; eauto.
  iNamed "Hblockmatch".
  iNamed "Htxn_in_hb".
  iDestruct (big_sepM2_lookup_acc with "Htxn_in_hb") as "[Hoff Htxn_in_hb]"; eauto.
  iNamed "Hoff".
  iDestruct ("Htxn_in_hb" with "[Hoff_own]") as "Htxn_in_hb"; eauto.
  iDestruct ("Hheapmatch" with "[Htxn_hb Htxn_in_hb]") as "Hheapmatch".
  { iExists _, _, _; iFrame. done. }

  iModIntro.
  iSplitR "Hmapsto_log Hmapsto_meta Hmod_frag".
  { iModIntro. iExists _, _, _. iFrame. }
  iModIntro.
  iSplitL.
  { iExists _. iFrame. }
  iPureIntro.
  unfold bufDataT_in_block in *.
  intuition eauto; congruence.
Qed.

End goose_lang.
