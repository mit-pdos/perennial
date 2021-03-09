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
Context `{!inG Σ (exclR unitO)}.

Implicit Types γ : aof_vol_names.
Implicit Types aof_ctx : (list u8) → iProp Σ.

Definition aof_lenN := nroot .@ "aof_len".
Definition aof_len_invariant γ : iProp Σ :=
  ∃ (l:u64),
    own γ.(len) (mono_nat_auth (1/2) (int.nat l)) ∗
    [∗ set] x ∈ (fin_to_set u64), x [[γ.(len_toks)]]↦ () ∨ ⌜int.nat x > int.nat l⌝
.

Definition aof_length_lb γ (l:u64) : iProp Σ :=
  own γ.(len) (mono_nat_lb (int.nat l)).

Definition aof_mu_invariant (aof_ptr:loc) γ aof_ctx : iProp Σ :=
  ∃ membuf_sl membufC predurableC (durlen:u64),
  "Hmembuf" ∷ aof_ptr ↦[AppendOnlyFile.S :: "membuf"] (slice_val membuf_sl) ∗
  "HdurableLength" ∷ aof_ptr ↦[AppendOnlyFile.S :: "durableLength"]{1/2} #durlen ∗
  "Hmembuf_sl" ∷ typed_slice.is_slice membuf_sl byteT 1 membufC ∗
  "Hpredurable" ∷ fmlist γ.(predurabledata) (1/2) predurableC ∗
  "Hlogdata" ∷ fmlist γ.(logdata) (1/2)%Qp (predurableC ++ membufC) ∗
  "Hlen_toks" ∷ ([∗ set] x ∈ (fin_to_set u64), x [[γ.(len_toks)]]↦ () ∨ ⌜int.nat x ≤ length (predurableC ++ membufC)⌝) ∗
  "Hmembuf_fupd" ∷ (aof_ctx predurableC ={⊤}=∗ aof_ctx (predurableC ++ membufC)
     ∗ (own γ.(len) (mono_nat_auth (1/2) (length predurableC)) ={⊤}=∗
        own γ.(len) (mono_nat_auth (1/2) (length (predurableC ++ membufC)))
       )
  ) ∗
  "#Hdurlen_lb" ∷ aof_length_lb γ durlen
.

Definition aofN := nroot .@ "aof".

Definition is_aof aof_ptr γ (aof_ctx : (list u8) → iProp Σ) : iProp Σ :=
  ∃ mu_ptr (lenCond_ptr durCond_ptr:loc),
  "#Hmu" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "mu"] mu_ptr) ∗
  "#HlengthCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "lengthCond"] #lenCond_ptr) ∗
  "#HdurableCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile.S :: "durableCond"] #durCond_ptr) ∗
  "#HlenCond" ∷ is_cond lenCond_ptr mu_ptr ∗
  "#HdurCond" ∷ is_cond durCond_ptr mu_ptr ∗
  "#Hmu_inv" ∷ is_lock aofN mu_ptr (aof_mu_invariant aof_ptr γ aof_ctx) ∗
  "#Haof_len_inv" ∷ inv aof_lenN (aof_len_invariant γ)
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

Lemma wp_AppendOnlyFile__Append aof_ptr γ data_sl aof_ctx (oldData newData:list u8) Q :
is_aof aof_ptr γ aof_ctx -∗
  {{{
       typed_slice.is_slice data_sl byteT 1 newData ∗ aof_log_own γ oldData ∗
       (aof_ctx oldData ={⊤}=∗ aof_ctx (oldData ++ newData) ∗ Q)
  }}}
    AppendOnlyFile__Append #aof_ptr (slice_val data_sl)
  {{{
       (l:u64), RET #l; aof_log_own γ (oldData ++ newData) ∗
                        (aof_length_lb γ l ={⊤}=∗ ▷ Q)
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

  rewrite -app_assoc.
  (* Want to prove membuf_fupd, and the postcondition *)
  set (membufC' := membufC ++ newData) in *.

  iAssert (([∗ set] x ∈ fin_to_set u64, x [[γ.(len_toks)]]↦ () ∨
                      ⌜int.nat x <= length (predurableC ++ membufC)⌝ ∨
                      ⌜length (predurableC ++ membufC') < int.nat x⌝
          ) ∗
          ([∗ set] x ∈ fin_to_set u64, x [[γ.(len_toks)]]↦ () ∨
                      ⌜int.nat x ≤ length (predurableC ++ membufC')⌝
          ))%I
    with "[Hlen_toks]"
    as "HH".
  {
    iApply big_sepS_sep.
    iApply (big_sepS_impl with "Hlen_toks").
    iModIntro.
    iIntros (x ?) "Hx".
    iDestruct "Hx" as "[Hx|%Hineq]".
    {
      destruct (bool_decide (length (predurableC ++ membufC') < int.nat x)) as [|] eqn:Hineq.
      {
        apply bool_decide_eq_true in Hineq.
        iSplitR "Hx".
        { iRight; iRight. done. }
        iLeft. iFrame.
      }
      {
        apply bool_decide_eq_false in Hineq.
        iSplitL "Hx".
        { iFrame. }
        iRight.
        iPureIntro.
        word.
      }
    }
    {
      iSplitL.
      {
        iRight; iLeft. done.
      }
      iRight. iPureIntro.
      replace (membufC') with (membufC ++ newData) by done.
      rewrite app_assoc.
      rewrite app_length.
      word.
    }
  }
  iDestruct "HH" as "[Htoks Hlen_toks]".

  assert (int.nat (U64 (length (predurableC ++ membufC'))) = (length (predurableC ++ membufC'))) as Hsafesize.
  { admit. (* TODO: This is where we need an overflow check. *) }
  assert ((length newData) > 0) by admit.
  (* TODO: add this to precondition *)

  iAssert (|={⊤}=> (
  aof_ctx predurableC
                   ={⊤}=∗ aof_ctx (predurableC ++ membufC')
                          ∗ (own γ.(len) (mono_nat_auth (1 / 2) (length predurableC))
                             ={⊤}=∗ own γ.(len)
                                      (mono_nat_auth (1 / 2)
                                         (length (predurableC ++ membufC'))))
  ) ∗ (aof_length_lb γ (U64 (length (predurableC ++ membufC'))) ={⊤}=∗ ▷ Q))%I with "[Hmembuf_fupd Hfupd Htoks]" as "HH".
  {
    (* allocate invariant to escrow Q *)
    iMod (own_alloc (Excl ())) as "HQtok".
    { done. }
    iDestruct "HQtok" as (γtok) "Htok".
    iMod (own_alloc (Excl ())) as "HQexcl".
    { done. }
    iDestruct "HQexcl" as (γq) "HQexcl".
    iDestruct (big_sepS_elem_of_acc _ _ (U64 (length (predurableC ++ membufC'))) with "Htoks") as "[Hlen_tok Hlen_toks_rest]".
    { set_solver. }
    iDestruct "Hlen_tok" as "[Hlen_tok|%Hbad]"; last first.
    {
      exfalso.
      rewrite Hsafesize in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      word.
    }
    iMod (inv_alloc aofN _ (own γtok (Excl ()) ∗ aof_length_lb γ (U64 (length (predurableC ++ membufC'))) ∨ (U64 (length (predurableC ++ membufC')) [[γ.(len_toks)]]↦ ()) ∨ Q ∗ own γq (Excl ())) with "[Hlen_tok]") as "#HQinv".
    {
      iRight. iLeft.
      iFrame.
    }
    iSplitR "Htok"; last first.
    {
      iModIntro.
      iIntros "Haof_lb".
      iInv "HQinv" as "Hq" "Hqclose".
      iDestruct "Hq" as "[>[Htok2 _]|Hq]".
      { iDestruct (own_valid_2 with "Htok Htok2") as %Hbad. contradiction. }
      iDestruct "Hq" as "[>Hlentok|Hq]".
      {
        iInv "Haof_len_inv" as ">Ha" "Haclose".
        unfold aof_len_invariant.
        iDestruct "Ha" as (l) "[Hlen Ha]".
        iDestruct (own_valid_2 with "Hlen Haof_lb") as %Hineq.
        apply mono_nat_both_frac_valid in Hineq as [_ Hineq].
        iDestruct (big_sepS_elem_of_acc _ _ (U64 (length (predurableC ++ membufC'))) with "Ha") as "[Ha Harest]".
        { set_solver. }
        iDestruct "Ha" as "[Hlentok2|%Hbad]"; last first.
        { exfalso. lia. }
        iDestruct (ptsto_conflict with "Hlentok Hlentok2") as %Hbad.
        done.
      }
      iMod ("Hqclose" with "[Htok Haof_lb]").
      { iLeft. iNext. iFrame. }
      iDestruct "Hq" as "[$ _]".
      by iModIntro.
    }

    iModIntro.
    iIntros "Hctx".
    iMod ("Hmembuf_fupd" with "Hctx") as "[Hctx Hmembuf_fupd]".
    iMod ("Hfupd" with "Hctx") as "[$ HQ]".
    iModIntro.

    (* length stuff *)
    iIntros "Hlen".
    iInv "HQinv" as "Hq" "Hqclose".
    iDestruct "Hq" as "[[_ >Hlb]|Hq]".
    {
      iDestruct (own_valid_2 with "Hlen Hlb") as %Hbad.
      exfalso.
      apply mono_nat_both_frac_valid in Hbad as [_ Hbad].
      rewrite Hsafesize in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      lia.
    }
    iDestruct "Hq" as "[>Hlen_tok|[_ >HQexcl2]]"; last first.
    { iDestruct (own_valid_2 with "HQexcl HQexcl2") as %Hbad. contradiction. }

    iDestruct ("Hlen_toks_rest" with "[$Hlen_tok]") as "Hlen_toks".
    iMod ("Hqclose" with "[HQexcl HQ]") as "_".
    { iRight; iRight; iFrame. }

    iMod ("Hmembuf_fupd" with "Hlen") as "Hlen".

    (* Use tokens to update mono_nat counter *)
    iInv "Haof_len_inv" as ">Ha" "Haclose".
    iDestruct "Ha" as (len) "[Hlen2 Ha]".
    iDestruct (own_valid_2 with "Hlen Hlen2") as %Hleneq.
    apply mono_nat_auth_frac_op_valid in Hleneq as [_ <-].
    iCombine "Hlen Hlen2" as "Hlen".
    rewrite mono_nat_auth_frac_op.
    rewrite Qp_half_half.
    iMod (own_update _ _ (mono_nat_auth 1 (length (predurableC ++ membufC'))) with "Hlen") as "Hlen".
    {
      apply mono_nat_update.
      repeat rewrite app_length.
      lia.
    }
    iEval (rewrite -Qp_half_half) in "Hlen".
    rewrite -mono_nat_auth_frac_op.
    iDestruct "Hlen" as "[Hlen Hlen2]".

    iMod ("Haclose" with "[Ha Hlen_toks Hlen2]") as "_".
    {
      iNext. iExists _. rewrite -Hsafesize.
      iFrame.
      iApply (big_sepS_impl with "[Ha Hlen_toks]").
      { iApply big_sepS_sep. iFrame. }

      iModIntro.
      iIntros (x ?) "Hx".
      destruct (bool_decide (int.nat (length (predurableC ++ membufC')) < int.nat x)) as [|] eqn:Hineq.
      {
        apply bool_decide_eq_true in Hineq.
        iRight.
        done.
      }
      {
        apply bool_decide_eq_false in Hineq.
        iLeft.
        iDestruct "Hx" as "[[$|%Hbad] [$|%Hineq2]]".
        exfalso.
        word.
      }
    }
    iFrame.
    by iModIntro.
  }

  iMod "HH" as "[Hmembuf_fupd HfupdQ]".

  iDestruct (typed_slice.is_slice_sz with "Hmembuf_sl") as %Hsz.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Haof_log HfupdQ]").
  {
    iFrame "#∗".
    iNext.
    iExists _, _, _, _.
    iFrame "#∗".
  }
  wp_pures.
  iApply "HΦ".
  iFrame.

Admitted.

End aof_proof.
