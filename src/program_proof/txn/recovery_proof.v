From Perennial.Helpers Require Import Transitions NamedProps Map.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.algebra Require Import auth_map log_heap.

From Goose.github_com.mit_pdos.goose_nfsd Require Import txn.
From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.
From Perennial.program_proof Require Import wal.specs wal.lib wal.heapspec addr.addr_proof buf.buf_proof disk_lib.
From Perennial.program_proof Require Import txn.invariant.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

Section goose_lang.
Context `{!txnG Σ}.

Implicit Types (γ: @txn_names Σ).

Definition txn_init_ghost_state γ : iProp Σ :=
  let logm0 := Build_async (∅: gmap addr object) [] in
  "logheap" ∷ log_heap_ctx (hG:=γ.(txn_logheap)) logm0 ∗
  "crashstates" ∷ ghost_var γ.(txn_crashstates) 1 logm0 ∗
  "metaheap" ∷ map_ctx γ.(txn_metaheap) 1 (∅ : gmap addr gname).

Lemma alloc_txn_init_ghost_state (γtxn_walnames: wal_heap_gnames) kinds :
  ⊢ |==> ∃ γ, ⌜γ.(txn_walnames) = γtxn_walnames⌝ ∗
              ⌜γ.(txn_kinds) = kinds⌝ ∗
              txn_init_ghost_state γ.
Proof.
  set (logm:=Build_async (∅: gmap addr object) []).
  iMod (seq_heap_init logm) as (txn_logheap) "[? _]".
  iMod (ghost_var_alloc logm) as (txn_crashstates) "?".
  iMod (map_init (∅ : gmap addr gname)) as (txn_metaheap) "?".
  iModIntro.
  iExists (Build_txn_names _ _ _ _ _ _).
  rewrite /txn_init_ghost_state /=.
  by iFrame.
Qed.

(* Definitely missing the durable invariant of the heapspec layer, which should
say something more complete about [γ.(txn_walnames)]. Otherwise there probably
isn't enough to relate the state inside [is_txn_always] to that in
[is_wal_inner_durable]. *)

Definition is_txn_durable γ dinit : iProp Σ :=
  ∃ ls',
  "His_wal_inner_durable" ∷ is_wal_inner_durable γ.(txn_walnames).(wal_heap_walnames) ls' dinit ∗
  "Hwal_res" ∷ wal_resources γ.(txn_walnames).(wal_heap_walnames) ∗
  "Hwal_heap_inv" ∷ wal_heap_inv γ.(txn_walnames) ls' ∗
  "Hlocked_walheap" ∷ is_locked_walheap γ.(txn_walnames) {| locked_wh_σd := ls'.(log_state.d);
                        locked_wh_σtxns := ls'.(log_state.txns);
                    |} ∗
  "His_txn_always" ∷ is_txn_always γ ∗
  ∃ crash_heaps,
  (* ⌜ lb < length ls'.(log_state.txns) ⌝%nat ∗ *)
  "Hcrash_heaps" ∷ ghost_var γ.(txn_walnames).(wal_heap_crash_heaps) (3/4) crash_heaps ∗
  "Hgh_ptsto" ∷ ([∗ map] a↦b ∈ latest crash_heaps, ∃ hb,
    ⌜hb_latest_update hb = b⌝ ∗
    mapsto (hG:=γ.(txn_walnames).(wal_heap_h)) a 1 hb).

Definition txn_exchanger (γ γ' : @txn_names Σ) : iProp Σ := True.

Global Instance is_txn_always_discretizable γ :
  Discretizable (is_txn_always γ).
Proof. apply _. Qed.

Global Instance is_txn_durable_discretizable γ dinit :
  Discretizable (is_txn_durable γ dinit).
Proof. apply _. Qed.

Theorem wpc_MkTxn (d:loc) dinit (γ:txn_names) logm k :
  {{{ is_txn_durable γ dinit ∗ ghost_var γ.(txn_crashstates) (3/4) logm }}}
    MkTxn #d @ k; ⊤
  {{{ (l: loc), RET #l; is_txn l γ dinit ∗ ([∗ map] a ↦ v ∈ latest (logm), mapsto_txn γ a v)
      (* cfupd stuff *) }}}
  {{{ ∃ γ', ⌜ txn_kinds γ' = txn_kinds γ ⌝ ∗ is_txn_durable γ' dinit ∗ txn_exchanger γ γ' }}}.
Proof.
  iIntros (Φ Φc) "(Hdur&Hlogm) HΦ".
  rewrite /MkTxn. wpc_pures.
  { crash_case. iNext. iExists γ. iSplit; first done. iFrame "Hdur". }

  iCache with "Hdur HΦ Hlogm".
  { crash_case.  iExists γ. iSplit; first done. iFrame "Hdur". }
  wpc_bind (lock.new _).
  wpc_frame; wp_apply (wp_new_free_lock).
  iIntros (lk) "Hlock". iNamed 1.
  wpc_bind (MkLog #d).
  iNamed "Hdur".
  iMod (alloc_heapspec_init_ghost_state (γ.(txn_walnames).(wal_heap_walnames)))
         as (γ'_txn_walnames ?) "Hheapspec_init".
  set (P := λ ls, (wal_heap_inv γ.(txn_walnames) ls ∗ heapspec_init_ghost_state γ'_txn_walnames)%I).
  (* TODO: need init_ghost_state for the txn so we can define γ', the new names *)
  iMod (alloc_txn_init_ghost_state γ'_txn_walnames γ.(txn_kinds)) as
      (γ' Hwalnames_eq Hkinds_eq) "Htxn_init".
  set (Prec (ls': log_state.t) :=
         (wal_heap_inv γ'.(txn_walnames) ls' ∗
          heapspec_resources γ.(txn_walnames) γ'.(txn_walnames) ls')%I).
  set (Pcrash (ls ls' : log_state.t) := (True)%I : iProp Σ).
  wpc_apply (wpc_MkLog_recover dinit P _ _ _ _ Prec Pcrash
            with "[] [$His_wal_inner_durable Hwal_res Hwal_heap_inv Hheapspec_init]").
  - iIntros "!>" (???) ">HP".
    iDestruct "HP" as "[Hinv Hinit]".
    iMod (wal_heap_inv_crash_transform with "Hinv Hinit") as "[Hinv Hres]"; eauto.
    rewrite /Prec /Pcrash.
    rewrite Hwalnames_eq.
    iModIntro.
    by iFrame.
  - iFrame.
  - iSplit.
    { iLeft in "HΦ".
      iModIntro. iNext.
      iIntros "Hcrash".
      iApply "HΦ".
      rewrite /P /Prec.
      iDestruct "Hcrash" as (γ'' ls'') "(Hdur' & Hres' & [HP|HP])".
      - admit.
      - admit. }
    iNext. iIntros (γ'' l) "(Hwal & Hwal_cfupd & Hwal_cinv)".
    wpc_frame "Hdur HΦ Hlogm".
    { admit. }
    rewrite -wp_fupd.
    wp_apply wp_allocStruct; first by val_ty.
    iIntros (txn_l) "Htxn".
    iApply struct_fields_split in "Htxn". iNamed "Htxn".
    wp_pures.
    iMod (readonly_alloc_1 with "mu") as "mu".
    iMod (readonly_alloc_1 with "log") as "log".
    iMod (alloc_lock lockN _ _ (is_txn_locked txn_l γ.(txn_walnames))
            with "Hlock [pos Hlocked_walheap]") as "Htxn_lock".
    { iNext. rewrite /is_txn_locked.
      iExists _, _, _; iFrame. }
    iModIntro.
    iNamed 1.
    iRight in "HΦ".
Admitted.

End goose_lang.
