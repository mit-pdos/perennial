From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import aof.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section aof_proof.
Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Class aofG Σ := LockserviceG {
  ls_rpcG :> inG Σ (prodR fracR (exclR (leibnizO (list u8)))) ;
}.

Record aof_vol_names := {
  logdata : gname ;
  predurabledata : gname ;
}.

Context `{!aofG Σ}.

Definition own_flist γ (q:Qp) (l:list u8) :=
  own γ (q, (Excl (l:leibnizO (list u8)))).

Implicit Types γ : aof_vol_names.

Definition aof_mu_invariant (aof_ptr:loc) γ : iProp Σ :=
  ∃ membuf_sl membufC predurableC (durlen:u64),
  "Hmembuf" ∷ aof_ptr ↦[AppendOnlyFile.S :: "membuf"] (slice_val membuf_sl) ∗
  "HdurableLength" ∷ aof_ptr ↦[AppendOnlyFile.S :: "durableLength"]{1/2} #durlen ∗
  "Hmembuf_sl" ∷ typed_slice.is_slice membuf_sl byteT 1 membufC ∗
  "Hpredurable" ∷ own_flist γ.(predurabledata) (1/2) predurableC ∗
  "Hlogdata" ∷ own_flist γ.(logdata) (1/2)%Qp (predurableC ++ membufC)
.

Definition aofN := nroot .@ "aof".

Definition is_aof aof_ptr γ : iProp Σ :=
  ∃ mu_ptr (lenCond_ptr durCond_ptr:loc),
  "#Hmu" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "mu"] mu_ptr) ∗
  "#HlengthCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "lengthCond"] #lenCond_ptr) ∗
  "#HdurableCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "durableCond"] #durCond_ptr) ∗
  "#HlenCond" ∷ is_cond lenCond_ptr mu_ptr ∗
  "#HdurCond" ∷ is_cond durCond_ptr mu_ptr ∗
  "#Hmu_inv" ∷ is_lock aofN mu_ptr (aof_mu_invariant aof_ptr γ)
.

(* TODO: upgrade to WPC *)
Lemma wp_CreateAppendOnlyFile (fname:string) :
  {{{
       (∃ data, fname f↦{1} data)
  }}}
    CreateAppendOnlyFile #(str fname)
  {{{
       aof_ptr γ, RET #aof_ptr; is_aof aof_ptr γ
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  wp_lam.

  wp_apply (wp_allocStruct).
  { admit. (* TODO: typechecking *) }
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "Hl".
  iNamed "Hl".

  wp_pures.
  Search (lock.new).
  wp_apply (wp_new_free_lock).
  iIntros (mu) "Hmu_free".

  wp_pures.
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (lengthCond) "[Hmu_free HlengthCond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (durableCond) "[Hmu_free HdurableCond]".
  wp_storeField.

  (* Interesting part of proof;
     One option is to keep the filemapsto, and also keep a ctx.
     Alternatively, we could give the filemapsto back, and require fupds giving
     us filemapsto as part of mu. I think keeping the ctx in the loop would be
     more "hocap" style.
   *)
  admit.
Admitted.

Definition aof_log_own γ data :=
  own_flist γ.(logdata) (1/2)%Qp data.

Lemma flist_combine (γ:gname) q q' data data' :
  own_flist γ q data -∗
  own_flist γ q' data' -∗
  own_flist γ (q + q') data.
Proof.
Admitted.

Lemma update_flist data' (γ:gname) data:
  own_flist γ 1 data ==∗
  own_flist γ 1 data'
.
Proof.
Admitted.

Lemma wp_AppendOnlyFile__Append aof_ptr γ data_sl (oldData newData:list u8) :
is_aof aof_ptr γ -∗
  {{{
       typed_slice.is_slice data_sl byteT 1 newData ∗ aof_log_own γ oldData
  }}}
    AppendOnlyFile__Append #aof_ptr (slice_val data_sl)
  {{{
       (l:u64), RET #l; aof_log_own γ (oldData ++ newData)
  }}}.
Proof.
  iIntros "#Haof" (Φ) "!# Hpre HΦ".
  iNamed "Haof".
  wp_lam.
  wp_pures.

  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Haof]".
  iNamed "Haof".
  iDestruct "Hpre" as "[HnewData Haof_log]".
  wp_pures.

  wp_loadField.
  wp_apply (typed_slice.wp_SliceAppendSlice (V:=u8) with "[$Hmembuf_sl $HnewData]").
  iIntros (membuf_sl') "Hmembuf_sl".
  wp_apply (wp_storeField with "Hmembuf").
  { unfold AppendOnlyFile.S. unfold field_ty. simpl. apply slice_val_ty. }
  iIntros "Hmembuf".

  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_slice_len).
  wp_pures.

  wp_loadField.
  wp_apply (wp_condSignal).
  { iFrame "#". }

  wp_pures.

  (* TODO: Update logical list *)

  wp_loadField.
  wp_apply (release_spec with "[-HΦ Haof_log]").
  {
    iFrame "#∗".
    iNext.
    iExists _, _, _, _.
    iFrame.
    (* update logical list above *)
    admit.
  }
  wp_pures.
  iApply "HΦ".
  (* same update as above *)
Admitted.

End aof_proof.
