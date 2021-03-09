From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import aof.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.algebra Require Import mlist auth_map.
From iris.algebra Require Import mono_nat.

Section aof_proof.
Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Class aofG Σ := AofG {
  aof_flistG :> fmlistG u8 Σ
}.

Record aof_vol_names := {
  logdata : gname ;
  predurabledata : gname ;
  len : gname ;
  len_toks : gname ;
}.

Context `{!aofG Σ}.
Context `{!inG Σ mono_natUR}.
Context `{!mapG Σ u64 unit}.

Implicit Types γ : aof_vol_names.
Implicit Types aof_ctx : (list u8) → iProp Σ.

Definition aof_len_invariant γ : iProp Σ :=
  ∃ (l:u64),
    own γ.(len) (mono_nat_auth (1/2) (int.nat l)) ∗
    [∗ set] x ∈ (fin_to_set u64), x [[γ.(len_toks)]]↦ () ∨ ⌜int.nat x > int.nat l⌝
.

Definition aof_mu_invariant (aof_ptr:loc) γ aof_ctx : iProp Σ :=
  ∃ membuf_sl membufC predurableC (durlen:u64),
  "Hmembuf" ∷ aof_ptr ↦[AppendOnlyFile.S :: "membuf"] (slice_val membuf_sl) ∗
  "HdurableLength" ∷ aof_ptr ↦[AppendOnlyFile.S :: "durableLength"]{1/2} #durlen ∗
  "Hmembuf_sl" ∷ typed_slice.is_slice membuf_sl byteT 1 membufC ∗
  "Hpredurable" ∷ fmlist γ.(predurabledata) (1/2) predurableC ∗
  "Hlogdata" ∷ fmlist γ.(logdata) (1/2)%Qp (predurableC ++ membufC) ∗
  "Hlen_toks" ∷ ([∗ set] x ∈ (fin_to_set u64), x [[γ.(len_toks)]]↦ () ∨ ⌜int.nat x < length (predurableC ++ membufC)⌝) ∗
  "Hmembuf_fupd" ∷ (aof_ctx predurableC ={⊤}=∗ aof_ctx (predurableC ++ membufC)
     ∗ (own γ.(len) (mono_nat_auth (1/2) (length predurableC)) ={⊤}=∗
        own γ.(len) (mono_nat_auth (1/2) (length (predurableC ++ membufC)))
       )
  )
.

Definition aofN := nroot .@ "aof".

Definition is_aof aof_ptr γ (aof_ctx : (list u8) → iProp Σ) : iProp Σ :=
  ∃ mu_ptr (lenCond_ptr durCond_ptr:loc),
  "#Hmu" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "mu"] mu_ptr) ∗
  "#HlengthCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "lengthCond"] #lenCond_ptr) ∗
  "#HdurableCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "durableCond"] #durCond_ptr) ∗
  "#HlenCond" ∷ is_cond lenCond_ptr mu_ptr ∗
  "#HdurCond" ∷ is_cond durCond_ptr mu_ptr ∗
  "#Hmu_inv" ∷ is_lock aofN mu_ptr (aof_mu_invariant aof_ptr γ aof_ctx)
.

(* TODO: upgrade to WPC *)
Lemma wp_CreateAppendOnlyFile (fname:string) data aof_ctx :
  {{{
       fname f↦{1} data ∗
       aof_ctx data
  }}}
    CreateAppendOnlyFile #(str fname)
  {{{
       aof_ptr γ, RET #aof_ptr; is_aof aof_ptr γ aof_ctx
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
  (*
    Going to go with hocap-style approach: seems easier to not lose any information in membuf_fupd.
    Otherwise, the membuf_fupd would say "|={Eo,Ei}=> fileptsto old ∗ fileptsto new ={Ei,Eo}=∗ emp",
    which isn't enough to chain with a new fupd.
   *)
  admit.
Admitted.

Definition aof_log_own γ data :=
  fmlist γ.(logdata) (1/2)%Qp data.

Definition aof_length_lb γ (l:u64) : iProp Σ.
Admitted.

Lemma wp_AppendOnlyFile__Append aof_ptr γ data_sl aof_ctx (oldData newData:list u8) Q :
is_aof aof_ptr γ aof_ctx -∗
  {{{
       typed_slice.is_slice data_sl byteT 1 newData ∗ aof_log_own γ oldData ∗
       (aof_ctx oldData ={⊤}=∗ aof_ctx (oldData ++ newData) ∗ Q)
  }}}
    AppendOnlyFile__Append #aof_ptr (slice_val data_sl)
  {{{
       (l:u64), RET #l; aof_log_own γ (oldData ++ newData) ∗
                        (aof_length_lb γ l ={⊤}=∗ Q)
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
  iDestruct "Hpre" as "(HnewData & Haof_log & Hfupd)".
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


  unfold aof_log_own.
  iDestruct (fmlist_agree_1 with "Haof_log Hlogdata") as %->.
  iCombine "Haof_log Hlogdata" as "Haof_log".

  iMod (fmlist_update ((predurableC ++ membufC) ++ newData) with "Haof_log") as "[Haof_log _]".
  { admit. (* have to prove list prefix... don't really care since we want flist, not fmlist *) }

  iDestruct "Haof_log" as "[Hlogdata Haof_log]".

  wp_loadField.
  wp_apply (release_spec with "[-HΦ Haof_log]").
  {
    iFrame "#∗".
    iNext.
    iExists _, _, _, _.
    rewrite -app_assoc.
    iFrame.

    iIntros "Haof_ctx".
    (* TODO: need to do this before, so we can also deal with the Q *)
    iMod ("Hmembuf_fupd" with "Haof_ctx") as "Haof_ctx".
    iMod ("Hfupd" with "Haof_ctx") as "[Haof_ctx HQ]".
    iModIntro.
    iFrame.
  }
  wp_pures.
  iApply "HΦ".
  iFrame.

  (* Need to set up mnat, tokens, and some invariants to prove this. *)
Admitted.

End aof_proof.
