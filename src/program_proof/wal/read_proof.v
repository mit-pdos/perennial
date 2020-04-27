From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Lemma memLogMap_ok_memLog_lookup memStart memLog a i :
  int.val memStart + Z.of_nat (length memLog) < 2^64 ->
  map_get (compute_memLogMap memLog memStart ∅) a = (i, true) ->
  ∃ b, memLog !! int.nat (word.sub i memStart) = Some (update.mk a b)
  (* also, i is the highest index such that this is true *).
Proof.
  intros Hbound Hlookup.
  apply map_get_true in Hlookup.
  assert (int.val memStart ≤ int.val i) by admit. (* from how memLogMap is computed and lack of overflow *)
  replace (int.nat (word.sub i memStart)) with (int.nat i - int.nat memStart)%nat by word.
  (* this is hard, induction is hard with this left fold *)
Admitted.

Opaque struct.t.

Theorem wp_WalogState__readMem γ (st: loc) σ (a: u64) :
  {{{ wal_linv_fields st σ ∗
      memLog_linv γ σ.(memStart) σ.(memLog) }}}
    WalogState__readMem #st #a
  {{{ b_s (ok:bool), RET (slice_val b_s, #ok);
      (if ok then ∃ b, is_block b_s b ∗
                       ⌜apply_upds σ.(memLog) ∅ !! int.val a = Some b⌝
      else ⌜b_s = Slice.nil⌝) ∗
      "Hfields" ∷ wal_linv_fields st σ ∗
      "HmemLog_linv" ∷ memLog_linv γ σ.(memStart) σ.(memLog)
  }}}.
Proof.
  iIntros (Φ) "(Hfields&HmemLog_inv) HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_call.
  wp_loadField.
  wp_apply (wp_MapGet with "His_memLogMap").
  iIntros (i ok) "(%Hmapget&His_memLogMap)".
  wp_pures.
  wp_if_destruct.
  - wp_apply util_proof.wp_DPrintf.
    wp_loadField. wp_loadField.
    apply memLogMap_ok_memLog_lookup in Hmapget as [b HmemLog_lookup];
      last by admit. (* TODO: in-bounds proof *)
    wp_apply (wp_SliceGet_updates with "[$His_memLog]"); eauto.
    simpl.
    iIntros ([a' u_s]) "(<-&Hb&His_memLog)".
    wp_apply (wp_copyUpdateBlock with "Hb").
    iIntros (s') "[Hb Hb_new]".
    iSpecialize ("His_memLog" with "Hb").
    wp_pures.
    iApply "HΦ".
    iFrame.
    simpl in HmemLog_lookup |- *.
    (* TODO: this comes from HmemLog_lookup plus that a' is maximal (the
    apply_upds formulation is actually a good way to phrase it, especially since
    [apply_upds] and [compute_memLogMap] are similar fold_left's) *)
Admitted.

Theorem simulate_read_mem {l γ Q σ memStart memLog b a} :
  apply_upds memLog ∅ !! int.val a = Some b ->
  (is_wal_inner l γ σ ∗ P σ) -∗
  memLog_linv γ memStart memLog -∗
  (∀ (σ σ' : log_state.t) mb,
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗ P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q mb) -∗
  |={⊤ ∖ ↑N}=> (is_wal_inner l γ σ ∗ P σ) ∗
              "HQ" ∷ Q (Some b) ∗
              "HmemLog_linv" ∷ memLog_linv γ memStart memLog.
Proof.
Admitted.

Theorem wp_Walog__ReadMem (Q: option Block -> iProp Σ) l γ a :
  {{{ is_wal P l γ ∗
       (∀ σₛ σₛ' mb,
         ⌜wal_wf σₛ⌝ -∗
         ⌜relation.denote (log_read_cache a) σₛ σₛ' mb⌝ -∗
         (P σₛ ={⊤ ∖ ↑N}=∗ P σₛ' ∗ Q mb))
   }}}
    Walog__ReadMem #l #a
  {{{ (ok:bool) bl, RET (slice_val bl, #ok); if ok
                                             then ∃ b, is_block bl b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  destruct_is_wal.
  wp_loadField.
  wp_apply (acquire_spec with "lk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
  iNamed "Hlkinv".
  wp_apply (wp_WalogState__readMem with "[$Hfields $HmemLog_linv]").
  iIntros (b_s ok) "(Hb&?&?)"; named.
  (* really meant to do wp_pure until wp_bind Skip succeeds *)
  do 8 wp_pure _; wp_bind Skip.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as (σs) "[Hinner HP]".
  wp_pures.
  destruct ok.
  - iDestruct "Hb" as (b) "[Hb %HmemLog_lookup]".
    iMod (simulate_read_mem HmemLog_lookup with "[$Hinner $HP] HmemLog_linv Hfupd")
      as "([Hinner HP]&?&?)"; named.
    iModIntro.
    iSplitL "Hinner HP".
    { iNext.
      iExists _; iFrame. }
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked HmemLog_linv Hfields HnextDiskEnd_txn]").
    { iExists _; iFrame "HdiskEnd_at_least Hstart_at_least ∗". }
    wp_pures.
    iApply "HΦ".
    iExists _; iFrame.
  - (* TODO: need a different simulation theorem (a much simpler one) *)
Abort.

End goose_lang.
