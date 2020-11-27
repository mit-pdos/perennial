From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.base_logic.lib Require Import mnat.

From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import auth_map log_heap.

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
    txn_metaheapG :> mapG Σ addr gname;
    txn_crashstatesG :> ghost_varG Σ (async (gmap addr object));
  }.

Record txn_names {Σ} := {
  txn_logheap : log_heapG addr object Σ;
  txn_metaheap : gname;
  txn_walnames : @wal_heap_gnames Σ;
  txn_crashstates : gname;
  txn_kinds : gmap u64 bufDataKind;
}.

Global Instance txn_names_eta {Σ} : Settable _ :=
  settable! (@Build_txn_names Σ) <txn_logheap;txn_metaheap;txn_walnames;txn_crashstates;txn_kinds>.

Section goose_lang.
Context `{!txnG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition lockN : namespace := nroot .@ "txnlock".
Definition invN : namespace := nroot .@ "txninv".

Definition mapsto_txn (γ : txn_names) (l : addr) (v : object) : iProp Σ :=
  ∃ γm,
    "Hmapsto_log" ∷ mapsto_cur (hG := γ.(txn_logheap)) l v ∗
    "Hmapsto_meta" ∷ ptsto_mut γ.(txn_metaheap) l 1 γm ∗
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
  iDestruct (ptsto_conflict with "H0m H1m") as %[].
Qed.

Definition bufDataT_in_block (walblock : Block) blockK (blkno off : u64) (bufData : {K & bufDataT K}) : Prop :=
  is_bufData_at_off walblock off (projT2 bufData) ∧
  valid_addr (Build_addr blkno off) ∧
  valid_off (projT1 bufData) off ∧
  blockK = projT1 bufData.

Definition bufDataTs_in_block (installed : Block) (bs : list Block) (blkno : u64) (blockK : bufDataKind)
                              (offmap : gmap u64 object)
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
                                   (offmap : gmap u64 object) : iProp Σ :=
  (* Very similar to txn_bufDataT_in_block *)
  ( [∗ map] off ↦ bufData ∈ offmap,
      ⌜ bufDataT_in_block walblock blockK blkno off bufData ⌝
  )%I.

Definition is_txn_state (γ:txn_names)
           (* the state of txn is these two variables *)
           (logm : async (gmap addr object))
           (crash_heaps: async (gmap u64 Block)) : iProp Σ :=
  ∃ (metam : gmap addr gname),
    "Hlogheapctx" ∷ log_heap_ctx (hG := γ.(txn_logheap)) logm ∗
    "Hcrashstates" ∷ ghost_var γ.(txn_crashstates) (1/4) logm ∗
    "Hmetactx" ∷ map_ctx γ.(txn_metaheap) 1 metam ∗
    "Hheapmatch" ∷ ( [∗ map] blkno ↦ offmap;metamap ∈ gmap_addr_by_block (latest logm);gmap_addr_by_block metam,
      ∃ installed bs blockK,
        "%Htxn_hb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
        "Htxn_hb" ∷ mapsto (hG := γ.(txn_walnames).(wal_heap_h)) blkno 1 (HB installed bs) ∗
        "Htxn_in_hb" ∷ bufDataTs_in_block installed bs blkno blockK offmap metamap ) ∗
    "Hcrashheaps" ∷ ghost_var γ.(txn_walnames).(wal_heap_crash_heaps) (3/4) crash_heaps ∗
    "Hcrashheapsmatch" ∷ ( [∗ list] logmap;walheap ∈ possible logm;possible crash_heaps,
      [∗ map] blkno ↦ offmap;walblock ∈ gmap_addr_by_block logmap;walheap,
        ∃ blockK,
          "%Htxn_cb_kind" ∷ ⌜ γ.(txn_kinds) !! blkno = Some blockK ⌝ ∗
          "Htxn_in_cb" ∷ bufDataTs_in_crashblock walblock blkno blockK offmap ).

Definition is_txn_always (γ : txn_names) : iProp Σ :=
  ∃ logm crash_heaps, is_txn_state γ logm crash_heaps.

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
  iInv invN as ">Halways".
  lazymatch goal with
  | |- envs_entails _ ?g =>
    lazymatch g with
    | context[bi_pure ?φ] =>
      iAssert (⌜φ⌝)%I as "#-#Hgoal"; [ | by iFrame ]
    end
  end.

  iNamed "H".
  iNamed "Halways".

  iDestruct (log_heap_valid_cur with "Hlogheapctx Hmapsto_log") as "%Hlogvalid".
  iDestruct (map_valid with "Hmetactx Hmapsto_meta") as "%Hmetavalid".

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
  iPureIntro.
  unfold bufDataT_in_block in *.
  intuition eauto; congruence.
Qed.

Theorem mapsto_txn_cur γ (a : addr) (v : {K & bufDataT K}) :
  mapsto_txn γ a v -∗
  mapsto_cur (hG := γ.(txn_logheap)) a v ∗
  (∀ v', mapsto_cur (hG := γ.(txn_logheap)) a v' -∗ mapsto_txn γ a v').
Proof.
  rewrite /mapsto_txn.
  iIntros "H". iNamed "H".
  iFrame.
  iIntros (v') "H". iExists _. iFrame.
Qed.

Theorem mapsto_txn_cur_map {A} γ (m : gmap addr A) (f : A -> {K & bufDataT K}) (xform : A -> A):
  ( [∗ map] a↦v ∈ m, mapsto_txn γ a (f v) ) -∗
  ( [∗ map] a↦v ∈ m, mapsto_cur (hG := γ.(txn_logheap)) a (f v)) ∗
  ( ([∗ map] a↦v ∈ xform <$> m, mapsto_cur (hG := γ.(txn_logheap)) a (f v)) -∗
    [∗ map] a↦v ∈ xform <$> m, mapsto_txn γ a (f v) ).
Proof.
  iIntros "Hm".
  iDestruct (big_sepM_mono _ (λ a v, mapsto_cur (hG := γ.(txn_logheap)) a (f v) ∗
                                    (mapsto_cur (hG := γ.(txn_logheap)) a (f (xform v)) -∗ mapsto_txn γ a (f (xform v))))%I with "Hm") as "Hm".
  2: iDestruct (big_sepM_sep with "Hm") as "[$ Hm1]".
  { iIntros (k x Hkx) "H". iDestruct (mapsto_txn_cur with "H") as "[$ H]".
    iIntros "H'". iApply "H". iFrame. }
  iIntros "Hm0".
  iDestruct (bi_iff_2 with "[Hm1]") as "Hm1".
  1: iApply (big_sepM_fmap _ (λ k x, mapsto_cur k (f x) -∗ mapsto_txn γ k (f x))%I).
  2: iDestruct (big_sepM_sep with "[$Hm0 $Hm1]") as "Hm".
  1: iFrame.
  iApply (big_sepM_mono with "Hm").
  iIntros (k x Hkx) "[H0 H1]". iApply "H1". iFrame.
Qed.

Theorem mapsto_txn_locked (γ : txn_names) l dinit lwh a data E :
  ↑invN ⊆ E ->
  ↑walN ⊆ E ∖ ↑invN ->
  is_wal (wal_heap_inv γ.(txn_walnames)) l (wal_heap_walnames γ.(txn_walnames)) dinit ∗
  inv invN (is_txn_always γ) ∗
  is_locked_walheap γ.(txn_walnames) lwh ∗
  mapsto_txn γ a data
  -∗ |NC={E}=>
    is_locked_walheap γ.(txn_walnames) lwh ∗
    mapsto_txn γ a data ∗
    ⌜ ∃ v, locked_wh_disk lwh !! int.Z a.(addrBlock) = Some v ⌝.
Proof.
  iIntros (H0 H1) "(#Hiswal & #Hinv & Hlockedheap & Hmapsto)".
  iInv "Hinv" as ">Htxnalways" "Hclo".
  iNamed "Htxnalways".
  iNamed "Hmapsto".
  iDestruct (map_valid with "Hmetactx Hmapsto_meta") as %Hvalid.
  eapply gmap_addr_by_block_lookup in Hvalid.
  destruct Hvalid as [offmap [Hmetam Hoffmap]].
  iDestruct (big_sepM2_lookup_2_some with "Hheapmatch") as (x) "%Hlm"; eauto.
  iDestruct (big_sepM2_lookup_acc with "Hheapmatch") as "[Hx Hheapmatch]"; eauto.
  iNamed "Hx".
  iMod (wal_heap_mapsto_latest with "[$Hiswal $Hlockedheap $Htxn_hb]") as "(Hlockedheap & Htxn_hb & %)"; eauto.
  iMod ("Hclo" with "[-Hlockedheap Hmapsto_log Hmapsto_meta Hmod_frag]").
  { iNext. iExists _, _, _. iFrame.
    iApply "Hheapmatch". iExists _, _, _. iFrame. iFrame "%". }
  iModIntro.
  iFrame.
  iSplitL.
  { iExists _. iFrame. }
  iExists _. done.
Qed.

End goose_lang.
