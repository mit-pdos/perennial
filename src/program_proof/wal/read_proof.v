From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

(* TODO: prove this using new compute_memLog, probably has enough theorems to do
it *)
Lemma memLogMap_ok_memLog_lookup memStart (memLog: list update.t) a i :
  int.val memStart + Z.of_nat (length memLog) < 2^64 ->
  map_get (compute_memLogMap memLog memStart) a = (i, true) ->
  ∃ b, memLog !! int.nat (word.sub i memStart) = Some (update.mk a b)
  (* also, i is the highest index such that this is true *).
Proof.
  intros Hbound Hlookup.
  apply map_get_true in Hlookup.
Admitted.

Opaque struct.t.

Theorem wp_WalogState__readMem γ (st: loc) σ (a: u64) :
  {{{ wal_linv_fields st σ ∗
      memLog_linv γ σ.(memLog) }}}
    WalogState__readMem #st #a
  {{{ b_s (ok:bool), RET (slice_val b_s, #ok);
      (if ok then ∃ b, is_block b_s 1 b ∗
                       ⌜apply_upds σ.(memLog).(slidingM.log) ∅ !! int.val a = Some b⌝
      else ⌜b_s = Slice.nil ∧ apply_upds σ.(memLog).(slidingM.log) ∅ !! int.val a = None⌝) ∗
      "Hfields" ∷ wal_linv_fields st σ ∗
      "HmemLog_linv" ∷ memLog_linv γ σ.(memLog)
  }}}.
Proof.
  iIntros (Φ) "(Hfields&HmemLog_inv) HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_call.
  wp_loadField.
Admitted.

Theorem simulate_read_cache_hit {l γ Q σ memLog b a} :
  apply_upds memLog.(slidingM.log) ∅ !! int.val a = Some b ->
  (is_wal_inner l γ σ ∗ P σ) -∗
  memLog_linv γ memLog -∗
  (∀ (σ σ' : log_state.t) mb,
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗ P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q mb) -∗
  |={⊤ ∖ ↑N}=> (is_wal_inner l γ σ ∗ P σ) ∗
              "HQ" ∷ Q (Some b) ∗
              "HmemLog_linv" ∷ memLog_linv γ memLog.
Proof.
Admitted.

Theorem simulate_read_cache_miss {l γ Q σ memLog a} :
  apply_upds memLog.(slidingM.log) ∅ !! int.val a = None ->
  (is_wal_inner l γ σ ∗ P σ) -∗
  memLog_linv γ memLog -∗
  (∀ (σ σ' : log_state.t) mb,
      ⌜wal_wf σ⌝
        -∗ ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗ P σ ={⊤ ∖ ↑N}=∗ P σ' ∗ Q mb) -∗
  |={⊤ ∖ ↑N}=> (∃ σ', is_wal_inner l γ σ' ∗ P σ') ∗
              "HQ" ∷ Q None ∗
              "HmemLog_linv" ∷ memLog_linv γ memLog.
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
                                             then ∃ b, is_block bl 1 b ∗ Q (Some b)
                                             else Q None}}}.
Proof.
  iIntros (Φ) "[#Hwal Hfupd] HΦ".
  destruct_is_wal.
  wp_loadField.
  wp_apply (acquire_spec with "lk"). iIntros "(Hlocked&Hlkinv)".
  wp_loadField.
  iNamed "Hlkinv".
  wp_apply (wp_WalogState__readMem with "[$Hfields $HmemLog_linv]").
  iIntros (b_s ok) "(Hb&?&?)"; iNamed.
  (* really meant to do wp_pure until wp_bind Skip succeeds *)
  do 8 wp_pure _; wp_bind Skip.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  iInv "Hwal" as (σs) "[Hinner HP]".
  wp_pures.
  destruct ok.
  - iDestruct "Hb" as (b) "[Hb %HmemLog_lookup]".
    iMod (fupd_intro_mask' _ (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
    iMod (simulate_read_cache_hit HmemLog_lookup with "[$Hinner $HP] HmemLog_linv Hfupd")
      as "([Hinner HP]&?&?)"; iNamed.
    iMod "HinnerN" as "_".
    iModIntro.
    iSplitL "Hinner HP".
    { iNext.
      iExists _; iFrame. }
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked HmemLog_linv Hfields HdiskEnd_circ Hstart_circ]").
    { iExists _; iFrame. }
    wp_pures.
    iApply "HΦ".
    iExists _; iFrame.
  - iDestruct "Hb" as "[-> %HmemLog_lookup]".
    iMod (fupd_intro_mask' _ (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
    iMod (simulate_read_cache_miss HmemLog_lookup with "[$Hinner $HP] HmemLog_linv Hfupd")
      as "(Hinv&?&?)"; iNamed.
    iMod "HinnerN" as "_".
    iModIntro.
    iFrame "Hinv".
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked HmemLog_linv Hfields HdiskEnd_circ Hstart_circ]").
    { iExists _; iFrame. }
    wp_pures.
    iApply "HΦ".
    iFrame.
Qed.

End goose_lang.
