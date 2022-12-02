From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import aof.
From Perennial.algebra Require Import mlist.
From iris.algebra Require Import mono_nat.
From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof.fencing Require Import map.
From Perennial.goose_lang Require Import crash_borrow.

From Perennial.program_proof Require Import marshal_stateless_proof.

Section aof_proof.
Context `{!heapGS Σ}.
Context `{!filesysG Σ}.

Class aofG Σ := AofG {
  aof_flistG :> fmlistG u8 Σ ;
  aof_mnatG :> inG Σ mono_natUR ;
  aof_mapG :> mapG Σ u64 unit ;
  aof_tokG :> inG Σ (exclR unitO) ;
  aof_stagedG :> stagedG Σ ; (* for crash borrows? *)
  aof_ghostG :> ghost_varG Σ unit ;
}.

Record aof_vol_names := mk_aof_vol_names {
  logdata : gname ;
  predurabledata : gname ;
  len : gname ;
  len_toks : gname ;
  close_tok: gname ;
  initdata : list u8 ;
}.

Context `{!aofG Σ}.

Implicit Types γ : aof_vol_names.
Implicit Types P: (list u8) → iProp Σ.

Definition aof_lenN := nroot .@ "aof_len".

Definition aof_len_invariant γ : iProp Σ :=
  ∃ (l:u64),
    own γ.(len) (●MN{#1/2} (int.nat l)) ∗
    [∗ set] x ∈ (fin_to_set u64), x ⤳[γ.(len_toks)] () ∨ ⌜int.nat x > int.nat l⌝
.

Definition aof_length_lb γ (l:u64) : iProp Σ :=
  own γ.(len) (mono_nat_lb (int.nat l)).

Definition list_safe_size (l:list u8) := int.nat (length l) = length l.

Definition aof_log_own γ data : iProp Σ :=
  fmlist γ.(logdata) (DfracOwn (1/2)) data ∗
  ghost_var γ.(close_tok) 1 ()
.

Definition aofN := nroot .@ "aof".

Definition aof_close_resources (aof_ptr:loc) γ P Pcrash fname : iProp Σ :=
  ∃ (isClosed closeRequested:bool),
  "HcloseRequested" ∷ aof_ptr ↦[AppendOnlyFile :: "closeRequested"] #closeRequested ∗
  "Hclosed" ∷ aof_ptr ↦[AppendOnlyFile :: "closed"] #isClosed ∗ (* other half owned by background thread *)
  "#HexpectedData" ∷ (if closeRequested then ∃ expectedData, (fmlist γ.(logdata) (DfracDiscarded) expectedData) else True) ∗
  "HfileEscrow" ∷ (if isClosed then
              inv aofN (∃ data, crash_borrow (fname f↦ data ∗ P data) (|={⊤}=> ∃ data', fname f↦ data' ∗ Pcrash data') ∗
                      fmlist γ.(logdata) DfracDiscarded data ∨
                      ghost_var γ.(close_tok) 1 ()
                     )
            else
                    True)
.

Definition aof_mu_invariant (aof_ptr:loc) γ fname P Pcrash : iProp Σ :=
  ∃ membuf_sl membufC predurableC (durlen:u64),
  let memlen := length (predurableC ++ membufC) in
  "#Hcrash_wand" ∷ □ (∀ data, P data ={⊤}=∗ Pcrash data) ∗
  "Hmembuf" ∷ aof_ptr ↦[AppendOnlyFile :: "membuf"] (slice_val membuf_sl) ∗
  "HdurableLength" ∷ aof_ptr ↦[AppendOnlyFile :: "durableLength"]{1/2} #durlen ∗
  "Hlength" ∷ aof_ptr ↦[AppendOnlyFile :: "length"] #(U64 memlen) ∗
  "Hmembuf_sl" ∷ typed_slice.is_slice membuf_sl byteT 1 membufC ∗

  "Hpredurable" ∷ fmlist γ.(predurabledata) (DfracOwn (1/2)) (γ.(initdata) ++ predurableC) ∗
  "Hlogdata" ∷ fmlist γ.(logdata) (DfracOwn (1/2)) (γ.(initdata) ++ predurableC ++ membufC) ∗
  "%Hlengthsafe" ∷ ⌜list_safe_size (predurableC ++ membufC)⌝ ∗
  "Hlen_toks" ∷ ([∗ set] x ∈ (fin_to_set u64), x ⤳[γ.(len_toks)] () ∨ ⌜int.nat x ≤ memlen⌝) ∗
  "Hmembuf_fupd" ∷ (P (γ.(initdata) ++ predurableC) ={⊤}=∗ P (γ.(initdata) ++ predurableC ++ membufC)
     ∗ (own γ.(len) (●MN{#1/2} (length predurableC)) ={⊤}=∗ own γ.(len) (●MN{#1/2} memlen)
       )
  ) ∗
  "#Hdurlen_lb" ∷ aof_length_lb γ durlen ∗
  "Hclose" ∷ aof_close_resources aof_ptr γ P Pcrash fname
.

Definition is_aof aof_ptr γ fname (P : (list u8) → iProp Σ) Pcrash : iProp Σ :=
  ∃ mu_ptr (lenCond_ptr durCond_ptr cloCond_ptr:loc),
  "#Hmu" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "mu"] mu_ptr) ∗
  "#HlengthCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "lengthCond"] #lenCond_ptr) ∗
  "#HdurableCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "durableCond"] #durCond_ptr) ∗
  "#HclosedCond" ∷ readonly (aof_ptr ↦[AppendOnlyFile :: "closedCond"] #cloCond_ptr) ∗
  "#HlenCond" ∷ is_cond lenCond_ptr mu_ptr ∗
  "#HdurCond" ∷ is_cond durCond_ptr mu_ptr ∗
  "#HcloCond" ∷ is_cond cloCond_ptr mu_ptr ∗
  "#Hmu_inv" ∷ is_lock aofN mu_ptr (aof_mu_invariant aof_ptr γ fname P Pcrash) ∗
  "#Haof_len_inv" ∷ inv aof_lenN (aof_len_invariant γ)
.

Lemma wp_CreateAppendOnlyFile (fname:string) data P Pcrash :
□(∀ data, P data ={⊤}=∗ Pcrash data) -∗
  {{{
       crash_borrow (fname f↦ data ∗ P data)
                    (|={⊤}=> ∃ data', fname f↦ data' ∗ Pcrash data')
  }}}
    CreateAppendOnlyFile #(str fname)
  {{{
       aof_ptr γ, RET #aof_ptr; is_aof aof_ptr γ fname P Pcrash ∗ aof_log_own γ data
  }}}.
Proof.
  iIntros "#Hcrash_wand !#" (Φ) "Hpre HΦ".
  wp_lam.

  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor. Opaque slice.T. }
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
  iIntros (lengthCond) "[Hmu_free #HlenCond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (durableCond) "[Hmu_free #HdurCond]".
  wp_storeField.

  wp_loadField.
  wp_apply (wp_newCond' with "Hmu_free").
  iIntros (closedCond) "[Hmu_free #HcloCond]".
  wp_storeField.

  iAssert ((|={⊤}=> ∃ γ, is_aof l γ fname P Pcrash ∗
                      fmlist γ.(predurabledata) (DfracOwn (1/2)) γ.(initdata) ∗
                      l ↦[AppendOnlyFile :: "durableLength"]{1/2} #0 ∗
                      own γ.(len) (●MN{#1/2} 0) ∗
                      aof_log_own γ γ.(initdata) ∗
                      ⌜data = γ.(initdata)⌝
                          )
          )%I with "[-Hpre HΦ]" as ">HH".
  { (* Allocate ghost state and invariants *)
    iMod (fmlist_alloc data) as (γlogdata) "[Hlogdata Hlogdata2]".
    iMod (fmlist_alloc data) as (γpredurabledata) "[Hpredurable Hpredurable2]".

    iMod (ghost_map_alloc_fin ()) as (γlen_toks) "Hlen_toks".
    iMod (own_alloc (●MN 0)) as (γlen) "[Hlen Hlen2]".
    { apply mono_nat_auth_valid. }
    iDestruct (own_mono _ _ (◯MN 0) with "Hlen2") as "#Hdurlen_lb".
    { apply mono_nat_included. }
    iDestruct "durableLength" as "[HdurableLength HdurableLength2]".
    iMod (ghost_var_alloc ()) as (γclose_tok) "Hclose_tok".

    set (γ:=mk_aof_vol_names γlogdata γpredurabledata γlen γlen_toks γclose_tok data).
    iExists γ.

    iAssert (
    ([∗ set] x ∈ fin_to_set u64,
      (x ⤳[γlen_toks] () ∨ ⌜int.nat x ≤ 0%nat⌝) ∗
      (x ⤳[γlen_toks] () ∨ ⌜int.nat x > 0%nat⌝))
      )%I with "[Hlen_toks]" as "HH".
    {
      iApply (big_sepS_impl with "Hlen_toks").
      iModIntro.
      iIntros.
      destruct (decide (int.nat x <= 0%nat)).
      {
        iSplitR; iFrame.
        iRight. iPureIntro. done.
      }
      assert (int.nat x > 0%nat) by word.
      iSplitL; iFrame.
      iRight. iPureIntro. done.
    }
    iDestruct (big_sepS_sep with "HH") as "[Hlen_toks Hlen_toks2]".

    iMod (inv_alloc aof_lenN _ (aof_len_invariant γ) with "[Hlen2 Hlen_toks2]") as "#Hinv".
    {
      iNext.
      iExists (U64 0).
      iFrame.
    }
    iMod (readonly_alloc_1 with "mu") as "#Hmu".
    iMod (readonly_alloc_1 with "durableCond") as "#HdurableCond".
    iMod (readonly_alloc_1 with "lengthCond") as "#HlengthCond".
    iMod (readonly_alloc_1 with "closedCond") as "#HclosedCond".

    iMod (alloc_lock _ _ _ (aof_mu_invariant l γ fname P Pcrash) with "Hmu_free [-Hlogdata2 HdurableLength2 Hpredurable2 Hlen Hclose_tok]") as "#HmuInv".
    {
      iNext.
      iExists (Slice.nil), [], [], (U64 0).
      iDestruct is_slice_zero as "$".
      simpl.
      rewrite app_nil_r.
      iFrame "∗#".
      iSplitR; first done.
      iSplitR.
      { by iIntros "$ !> $ !>". }
      iExists false, false.
      iFrame.
      done.
    }
    iModIntro.
    iFrame.
    iSplitL; last done.
    iExists _, _, _, _.
    iFrame "#".
  }
  iDestruct "HH" as (γ) "(#His_aof & Hpredur & HdurLen & Hlen & Hlog_own & %Hre)".
  rewrite Hre.
  clear dependent data.
  wp_apply (wp_fork with "[-HΦ Hlog_own]").
  {
    iNext.
    iClear "HlenCond HdurCond HcloCond Hcrash_wand".
    iNamed "His_aof".
    wp_loadField.
    wp_apply (acquire_spec with "Hmu_inv").
    iIntros "[Hlocked Haof_own]".
    wp_pures.
    iAssert (∃ data',
              crash_borrow (fname f↦ (γ.(initdata) ++ data') ∗ P (γ.(initdata) ++ data'))
                           (|={⊤}=> ∃ data2, fname f↦ data2 ∗ Pcrash data2) ∗
              fmlist γ.(predurabledata) (DfracOwn (1/2)) (γ.(initdata) ++ data') ∗
              l ↦[AppendOnlyFile :: "durableLength"]{1 / 2} #(U64 (length data')) ∗
              own γ.(len) (●MN{#1/2} (length (data')))
            )%I with "[Hpre Hpredur HdurLen Hlen]" as "Hfile_ctx".
    { iExists []; iFrame. rewrite app_nil_r. iFrame. }
    wp_forBreak.
    wp_pures.

    iNamed "Haof_own".
    wp_loadField.
    wp_apply (wp_slice_len).

    iNamed "Hclose".
    wp_apply (wp_and with "[HcloseRequested]").
    { iNamedAccu. }
    {
      wp_pures.
      done.
    }
    {
      iIntros.
      wp_loadField.
      wp_pures.
      iFrame.
      instantiate (2:=(closeRequested = false)).
      iPureIntro.
      f_equal.
      destruct closeRequested.
      { rewrite bool_decide_false; done. }
      { rewrite bool_decide_true; done. }
    }
    iNamed 1.

    wp_pures.

    wp_if_destruct.
    {
      wp_loadField.
      wp_apply (wp_condWait with "[- Hfile_ctx]").
      { iFrame "#∗". iExists _, _, _, _; iFrame "∗#". iSplitR; first done.
        iExists _, _; iFrame "∗#".
      }
      iIntros "[Hlocked Haof_own]".
      wp_pures.
      iLeft.
      iFrame.
      done.
    }

    wp_loadField.

    (* Prepare ghost state for writing to file; whether we close the file or
       not, we're going to do the FileAppend *)
    iDestruct "Hfile_ctx" as (data') "(Hfile_ctx & Hpredur & HdurLen & Hlen)".
    iDestruct (fmlist_agree_1 with "Hpredur Hpredurable") as %Hpredur.
    apply app_inv_head in Hpredur.
    rewrite Hpredur.
    iCombine "Hpredur Hpredurable" as "Hpredur".
    iMod (fmlist_update (γ.(initdata) ++ predurableC ++ membufC) with "Hpredur") as "[Hpredur _]".
    { rewrite app_assoc. apply prefix_app_r. done. }
    iDestruct "Hpredur" as "[Hpredur Hpredurable]".

    wp_if_destruct.
    { (* case: close aof; write the remaining stuff first, using the same
         arugment as when we write with the lock *)
      wp_loadField.

      wp_bind (FileAppend _ _).
      iApply (wpc_wp _ _ _ _ True).
      wpc_apply (wpc_crash_borrow_open_modify with "Hfile_ctx").
      { done. }
      iSplit; first done.
      iIntros "[Hfile Hctx]".
      iApply wpc_fupd.

      iDestruct (is_slice_to_small with "Hmembuf_sl") as "Hmembuf_sl".
      wpc_apply (wpc_FileAppend with "[$Hfile $Hmembuf_sl]").
      { admit. } (* TODO: list length overflow.
                  This seems a bit tricky. γ.initdata is the initial contents of
                  the file, which could be arbitrarily large. So, this could
                  actually overflow, and we can't even add an
                  std.AssumeNoOverflow to the code without first reading the
                  size of the file.
                  *)
      iSplit.
      { (* This is the case in which the node crashes during the FileAppend. *)
        iIntros "[Hbefore|Hafter]".
        {
          iSplitR; first done.
          iMod ("Hcrash_wand" with "[$Hctx]") as "HH".
          iModIntro. iExists _; iFrame.
        }
        {
          iSplitR; first done.
          iExists _; iFrame.
          iMod ("Hmembuf_fupd" with "Hctx") as "[Hctx _]".
          rewrite app_assoc.
          iApply "Hcrash_wand".
          iFrame.
        }
      }
      iNext.
      iIntros "[Hfile _]".
      iMod ("Hmembuf_fupd" with "Hctx") as "[Hctx Hlen_fupd]".
      iMod ("Hlen_fupd" with "Hlen") as "Hlen".
      iEval (rewrite mono_nat_auth_lb_op) in "Hlen".
      iDestruct "Hlen" as "[Hlen #Hlenlb]".

      iModIntro.
      iExists _.
      iSplitL "Hfile Hctx".
      { iAccu. }
      iSplit.
      {
        iModIntro. iIntros "[Hfile HP]".
        iExists _. rewrite app_assoc.
        iFrame. iApply "Hcrash_wand". iFrame.
      }

      iIntros "Hfile_ctx".
      iSplit; first done.
      wp_pures.

      wp_apply (wp_NewSlice).
      iIntros (empty_membuf_sl) "Hmembuf_empty".
      wp_storeField.

      wp_loadField.

      iDestruct (struct_field_mapsto_agree with "HdurLen HdurableLength") as %Heq.
      rewrite Heq.
      iCombine "HdurLen HdurableLength" as "HdurLen".
      wp_storeField.
      wp_loadField.
      wp_apply (wp_condBroadcast).
      { iFrame "#". }
      wp_pures.
      wp_storeField.
      wp_loadField.
      wp_apply (wp_condBroadcast).
      { iFrame "#". }
      wp_pures.
      wp_loadField.
      iNamed "Hclose".
      iDestruct "HexpectedData" as (?) "HexpectedData".
      iDestruct (fmlist_agree_1 with "HexpectedData Hlogdata") as %->.

      iMod (inv_alloc with "[Hfile_ctx]") as "#HfileEscrow2".
      {
        instantiate (1:=(∃ data : list u8,
                       crash_borrow (fname f↦data ∗ P data)
                       (|={⊤}=> ∃ data'0 : list u8, fname f↦data'0 ∗ Pcrash data'0) ∗
                       fmlist γ.(logdata) DfracDiscarded data ∨ ghost_var γ.(close_tok) 1 ())%I).
        iNext.
        rewrite -app_assoc.
        iExists _.
        iLeft.
        iFrame "∗#".
      }

      wp_apply (release_spec with "[-Hlen]").
      {
        iFrame "#∗".
        iNext.
        iDestruct "HdurLen" as "[HdurableLength HdurLen]".
        iExists _, [], _, _.
        rewrite app_nil_r.
        iFrame "∗#%".
        iSplitR.
        { by iIntros "$ !> $ !>". }
        unfold aof_length_lb.
        rewrite Hlengthsafe.
        iFrame "#".

        iExists _, _.
        iFrame "Hclosed ∗".
        iFrame "#".
        iExists _; iFrame "#".
      }
      wp_pures.
      iRight.
      done.
    }

    (* case: don't want to close the file, do a FileAppend after letting go of
       mutex and loop *)
    wp_loadField.
    wp_pures.
    wp_loadField.
    wp_pures.

    wp_apply (wp_new_slice).
    { done. }
    iIntros (empty_membuf_sl) "Hmembuf_empty".
    wp_apply (wp_storeField with "Hmembuf").
    { unfold AppendOnlyFile. unfold field_ty. simpl. apply slice_val_ty. }
    iIntros "Hmembuf".

    wp_pures.
    wp_loadField.

    wp_apply (release_spec with "[-Hfile_ctx Hpredur Hmembuf_fupd Hmembuf_sl HdurLen Hlen]").
    { iFrame "#∗". iNext. iExists _, [], (predurableC ++ membufC), _. iFrame "∗#".
      rewrite app_nil_r.
      iFrame.
      iSplitL ""; first done.
      iSplitR.
      { iIntros "$ !> $ !> //". }
      iExists _, _; iFrame "∗#".
    }

    wp_pures.

    iDestruct (typed_slice.is_slice_sz with "Hmembuf_sl") as %Hsz.
    iDestruct (is_slice_to_small with "Hmembuf_sl") as "Hmembuf_sl".

    wp_bind (FileAppend _ _).
    iApply (wpc_wp _ _ _ _ True).
    wpc_apply (wpc_crash_borrow_open_modify with "Hfile_ctx").
    { done. }
    iSplit; first done.
    iIntros "[Hfile Hctx]".
    iApply wpc_fupd.

    wpc_apply (wpc_FileAppend with "[$Hfile $Hmembuf_sl]").
    { admit. } (* TODO: list length overflow.
                  This seems a bit tricky. γ.initdata is the initial contents of
                  the file, which could be arbitrarily large. So, this could
                  actually overflow, and we can't even add an
                  std.AssumeNoOverflow to the code without first reading the
                  size of the file.
                *)
    iSplit.
    { (* This is the case in which the node crashes during the FileAppend. *)
      iIntros "[Hbefore|Hafter]".
      {
        iSplitR; first done.
        iExists _; iFrame.
        iApply "Hcrash_wand". iFrame.
      }
      {
        iSplitR; first done.
        iExists _; iFrame.
        iMod ("Hmembuf_fupd" with "Hctx") as "[Hctx _]".
        rewrite app_assoc.
        iApply "Hcrash_wand". iFrame.
      }
    }
    iNext.
    iIntros "[Hfile _]".
    iMod ("Hmembuf_fupd" with "Hctx") as "[Hctx Hlen_fupd]".
    iModIntro.
    iExists _.
    iSplitL "Hfile Hctx".
    { iNamedAccu. }
    iSplit.
    {
      iModIntro. iNamed 1.
      iExists _. rewrite app_assoc.
      iFrame. iApply "Hcrash_wand". iFrame.
    }

    iIntros "Hfile_ctx".
    iSplit; first done.

    wp_pures.
    wp_loadField.
    wp_apply (acquire_spec with "Hmu_inv").
    iIntros "[Hlocked Haof_own]".
    iRename "Hdurlen_lb" into "Hdurlen_lb_old".
    iClear "Hcrash_wand".
    iNamed "Haof_own".
    wp_pures.

    iDestruct (struct_field_mapsto_agree with "HdurLen HdurableLength") as %Heq.
    rewrite Heq.
    iCombine "HdurLen HdurableLength" as "HdurLen".
    wp_storeField.

    wp_loadField.
    iMod ("Hlen_fupd" with "Hlen") as "Hlen".
    iEval (rewrite mono_nat_auth_lb_op) in "Hlen".
    iDestruct "Hlen" as "[Hlen #Hlenlb]".

    wp_apply (wp_condBroadcast).
    { iFrame "#". }
    wp_pures.
    iLeft.
    iFrame.
    iSplitL ""; first done.
    iDestruct "HdurLen" as "[HdurableLength HdurLen]".
    iSplitR "Hpredur HdurLen Hlen Hfile_ctx".
    {
      iExists _, _, _, _; iFrame "∗#".
      unfold aof_length_lb.
      iSplitL ""; first done.
      unfold aof_length_lb.
      rewrite Hlengthsafe.
      iFrame "#".
      done.
    }
    {
      rewrite -Hpredur.
      repeat rewrite -app_assoc.
      iExists _; iFrame.
      done.
    }
  }
  wp_pures.
  iApply "HΦ".
  iFrame "∗#".
  done.
Admitted.

Lemma wp_AppendOnlyFile__Append Q aof_ptr γ data_sl P Pcrash fname (oldData newData:list u8) q :
length newData > 0 →
list_safe_size newData →
is_aof aof_ptr γ fname P Pcrash -∗
  {{{
       typed_slice.is_slice_small data_sl byteT q newData ∗ aof_log_own γ oldData ∗
       (P oldData ={⊤}=∗ P (oldData ++ newData) ∗ Q)
  }}}
    AppendOnlyFile__Append #aof_ptr (slice_val data_sl)
  {{{
       (l:u64), RET #l; aof_log_own γ (oldData ++ newData) ∗
                        (aof_length_lb γ l ={⊤}=∗ ▷ Q)
  }}}.
Proof.
  intros HnewDataLen HnewDataSafe.
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
  iDestruct (is_slice_small_sz with "HnewData") as %Hsz.

  wp_apply (wp_WriteBytes with "[$Hmembuf_sl $HnewData]").
  iIntros (membuf_sl') "[Hmembuf_sl HnewData]".
  wp_apply (wp_storeField with "Hmembuf").
  { unfold AppendOnlyFile. unfold field_ty. simpl. apply slice_val_ty. }
  iIntros "Hmembuf".

  wp_pures.

  (* overflow guard *)
  wp_apply (wp_slice_len).
  wp_loadField.
  wp_apply (std_proof.wp_SumAssumeNoOverflow).
  iIntros (HnoOverflow).
  wp_storeField.

  wp_loadField.
  wp_pures.
  rewrite -HnewDataSafe in Hsz.
  assert (U64 (length newData) = data_sl.(Slice.sz)) as HH.
  {
    apply Z2Nat.inj in Hsz.
    { word_cleanup. naive_solver. }
    { word_cleanup. naive_solver. }
    word.
  }
  rewrite -HH.
  rewrite -HH in HnoOverflow.
  wp_pures.
  wp_loadField.
  wp_apply (wp_condSignal).
  { iFrame "#". }

  wp_pures.

  unfold aof_log_own.
  iDestruct "Haof_log" as "[Haof_log Htok]".
  iDestruct (fmlist_agree_1 with "Haof_log Hlogdata") as %->.
  iCombine "Haof_log Hlogdata" as "Haof_log".

  iMod (fmlist_update ((γ.(initdata) ++ predurableC ++ membufC) ++ newData) with "Haof_log") as "[Haof_log _]".
  { apply prefix_app_r. done. }

  iDestruct "Haof_log" as "[Hlogdata Haof_log]".

  rewrite -app_assoc.
  (* Want to prove membuf_fupd, and the postcondition *)
  set (membufC' := membufC ++ newData) in *.

  iAssert (([∗ set] x ∈ (fin_to_set u64 : gset u64), x ⤳[γ.(len_toks)] () ∨
                      ⌜int.nat x <= length (predurableC ++ membufC)⌝ ∨
                      ⌜length (predurableC ++ membufC') < int.nat x⌝
          ) ∗
          ([∗ set] x ∈ (fin_to_set u64 : gset u64), x ⤳[γ.(len_toks)] () ∨
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

  assert (int.nat (U64 (length (predurableC ++ membufC'))) = (length (predurableC ++ membufC'))) as Hsafesize'.
  {
    replace (membufC') with (membufC ++ newData) by done.
    rewrite app_assoc.
    rewrite app_length.
    word_cleanup.
    rewrite -Hlengthsafe.
    repeat (rewrite Nat2Z.inj_add).
    replace (length newData) with (Z.to_nat (Z.of_nat (length newData))) by lia.
    rewrite -Z2Nat.inj_add.
    {
      rewrite Z2Nat.inj_iff.
      {
        rewrite Z2Nat.id.
        {
          rewrite wrap_small; first word.
          split.
          {
            apply Z.add_nonneg_nonneg; word_cleanup; naive_solver.
          }
          {
            rewrite Nat2Z.id.
            rewrite -HnewDataSafe.
            replace (Z.of_nat (int.nat (length newData))) with (int.Z (length newData)); last first.
            { rewrite u64_Z_through_nat. done. }
            destruct (bool_decide (int.Z (length (predurableC ++ membufC)) + (int.Z (length newData)) < 2 ^ 64))%Z eqn:Hnov.
            { apply bool_decide_eq_true in Hnov. done. }
            {
              apply bool_decide_eq_false in Hnov.
              word.
            }
          }
        }
        naive_solver.
      }
      {
        word_cleanup.
        unfold word.wrap.
        by apply Z_mod_lt.
      }
      {
        word_cleanup.
        apply Z.add_nonneg_nonneg; word_cleanup; naive_solver.
      }
    }
    { naive_solver. }
    { lia. }
  }

  iAssert (|={⊤}=> (P (γ.(initdata) ++ predurableC)
                   ={⊤}=∗ P (γ.(initdata) ++ predurableC ++ membufC')
                          ∗ (own γ.(len) (●MN{#1/2} (length predurableC))
                             ={⊤}=∗ own γ.(len)
                                      (●MN{#1/2} (length (predurableC ++ membufC'))))
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
      rewrite Hsafesize' in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      rewrite app_length in Hbad.
      word.
    }
    iMod (inv_alloc aofN _ (own γtok (Excl ()) ∗ aof_length_lb γ (U64 (length (predurableC ++ membufC'))) ∨ (U64 (length (predurableC ++ membufC')) ⤳[γ.(len_toks)] ()) ∨ Q ∗ own γq (Excl ())) with "[Hlen_tok]") as "#HQinv".
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
        apply mono_nat_both_dfrac_valid in Hineq as [_ Hineq].
        iDestruct (big_sepS_elem_of_acc _ _ (U64 (length (predurableC ++ membufC'))) with "Ha") as "[Ha Harest]".
        { set_solver. }
        iDestruct "Ha" as "[Hlentok2|%Hbad]"; last first.
        { exfalso. lia. }
        iDestruct (ghost_map_points_to_valid_2 with "Hlentok Hlentok2") as %[Hbad _].
        exfalso.
        rewrite dfrac_op_own in Hbad.
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
    rewrite -app_assoc.
    iMod ("Hfupd" with "Hctx") as "[$ HQ]".
    iModIntro.

    (* length stuff *)
    iIntros "Hlen".
    iInv "HQinv" as "Hq" "Hqclose".
    iDestruct "Hq" as "[[_ >Hlb]|Hq]".
    {
      iDestruct (own_valid_2 with "Hlen Hlb") as %Hbad.
      exfalso.
      apply mono_nat_both_dfrac_valid in Hbad as [_ Hbad].
      rewrite Hsafesize' in Hbad.
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
    apply mono_nat_auth_dfrac_op_valid in Hleneq as [_ <-].
    iCombine "Hlen Hlen2" as "Hlen".
    iMod (own_update _ _ (mono_nat_auth _ (length (predurableC ++ membufC'))) with "Hlen") as "Hlen".
    {
      apply mono_nat_update.
      repeat rewrite app_length.
      lia.
    }
    iDestruct "Hlen" as "[Hlen Hlen2]".

    iMod ("Haclose" with "[Ha Hlen_toks Hlen2]") as "_".
    {
      iNext. iExists _. rewrite -Hsafesize'.
      iFrame.
      iApply (big_sepS_impl with "[Ha Hlen_toks]").
      { iApply big_sepS_sep. iFrame. }

      iModIntro.
      iIntros (x ?) "Hx".
      destruct (bool_decide (int.nat (length (predurableC ++ membufC')) < int.nat x)) as [|] eqn:Hineq.
      {
        apply bool_decide_eq_true in Hineq.
        iRight.
        iPureIntro.
        word.
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

  wp_loadField.
  wp_apply (release_spec with "[-HΦ Haof_log HfupdQ Htok]").
  {
    iFrame "#∗".
    iNext.
    iExists _, _, _, _.
    rewrite -app_assoc.
    iFrame "∗#".
    replace (word.add (length (predurableC ++ membufC)) (length newData)) with
        (U64 (length (predurableC ++ membufC'))); last first.
    {
      repeat rewrite app_length.
      rewrite -word.ring_morph_add.
      word_cleanup.
      repeat (rewrite Nat2Z.inj_add).
      rewrite Z.add_assoc.
      done.
    }
    iFrame.
    done.
  }
  wp_pures.
  iApply "HΦ".
  iFrame.
  iModIntro.
  iIntros "#Hlb".
  iMod ("HfupdQ" with "[Hlb]") as "$"; last by iModIntro.
  replace (U64 (length (predurableC ++ membufC'))) with
      (word.add (length (predurableC ++ membufC)) (length newData)).
  { iFrame "#". }

  repeat rewrite app_length.
  repeat (rewrite Nat2Z.inj_add).
  rewrite Z.add_assoc.
  rewrite -word.ring_morph_add.
  unfold U64.
  done.
Qed.

Lemma wp_AppendOnlyFile__WaitAppend aof_ptr γ (l:u64) fname P Pcrash :
is_aof aof_ptr γ fname P Pcrash -∗
  {{{
       True
  }}}
    AppendOnlyFile__WaitAppend #aof_ptr #l
  {{{
       RET #(); aof_length_lb γ l
  }}}.
Proof.
  iIntros "#Haof" (Φ) "!# _ HΦ".
  wp_lam.
  wp_pures.
  iNamed "Haof".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Haof_own]".
  wp_pures.
  wp_apply (wp_forBreak_cond' with "[-]").
  {
    iNamedAccu.
  }
  iModIntro.
  iNamed 1.

  wp_pures.
  iNamed "Haof_own".
  wp_loadField.
  wp_pures.
  wp_if_destruct.
  {
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[- HΦ]").
    {
      iFrame "#∗".
      iExists _, _, _, _. iFrame "#∗".
      done.
    }
    iIntros "[Hlocked Haof_own]".
    wp_pures.
    iLeft.
    iFrame.
    done.
  }
  iSpecialize ("HΦ" with "[Hdurlen_lb]").
  {
    assert (int.nat l ≤ int.nat durlen) as Hineq.
    {
      word.
    }
    unfold aof_length_lb.
    replace (int.nat durlen)%nat with ((int.nat durlen) `max` int.nat l)%nat by word.
    rewrite mono_nat_lb_op.
    iDestruct "Hdurlen_lb" as "[_ $]".
  }
  iRight.
  iSplitL ""; first done.
  iModIntro.
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[- HΦ]").
  {
    iFrame "#∗".
    iExists _, _, _, _. iFrame "#∗".
    done.
  }
  wp_pures.
  iApply "HΦ".
Qed.

Lemma wp_AppendOnlyFile__Close aof_ptr γ P Pcrash fname data :
is_aof aof_ptr γ fname P Pcrash -∗
  {{{
       aof_log_own γ data
  }}}
    AppendOnlyFile__Close #aof_ptr
  {{{
       RET #(); crash_borrow (fname f↦ data ∗ P data) (|={⊤}=> ∃ data', fname f↦ data' ∗ Pcrash data')
  }}}.
Proof.
  iIntros "#Haof" (Φ) "!# Haof_log HΦ".
  wp_lam.
  wp_pures.
  iNamed "Haof".
  wp_loadField.
  wp_apply (acquire_spec with "Hmu_inv").
  iIntros "[Hlocked Haof_own]".
  wp_pures.
  iNamed "Haof_own".
  iNamed "Hclose".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_condSignal).
  { iFrame "#". }
  wp_pures.

  iDestruct "Haof_log" as "[Haof_log Htok]".
  iMod (fmlist_freeze with "Haof_log") as "#Hexpected".

  iAssert (aof_mu_invariant aof_ptr γ fname P Pcrash) with "[-Htok HΦ Hlocked]" as "Haof_own".
  {
    iExists _, _, _, _.
    iFrame "∗#%".
    iExists _, _.
    iFrame "HcloseRequested ∗%".
    iDestruct "Hclose" as "[_ $]".
    iExists _; iFrame "#".
  }

  wp_forBreak_cond.

  iClear "Hdurlen_lb Hcrash_wand".
  iNamed "Haof_own".
  iNamed "Hclose".
  wp_loadField.
  wp_if_destruct.
  { (* aof not closed yet, keep looping *)
    wp_pures.
    wp_loadField.
    wp_apply (wp_condWait with "[-Htok HΦ]").
    {
      iFrame "#∗".
      iExists _, _, _, _.
      iFrame "∗#%".
      iExists _, _.
      iFrame "∗#∗".
    }
    iIntros "[Hlocked Haof_own]".
    wp_pures.
    iLeft.
    iSplitR; first done.
    iModIntro.
    iFrame.
  }
  (* aof closed *)
  iRight.
  iModIntro.
  iSplitR; first done.
  iDestruct "Hclose" as "[HcloseRest #H]".
  iNamed "H".

  wp_pure1_credit "Hlc".
  iApply fupd_wp.
  iInv "HfileEscrow" as "Hi" "Hiclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iDestruct "Hi" as (?) "[[Hf #Hdata]|Hbad]"; last first.
  {
    iDestruct (ghost_var_valid_2 with "Htok Hbad") as %Hbad.
    exfalso. naive_solver.
  }
  iMod ("Hiclose" with "[$Htok]").
  { done. }
  iModIntro.

  iDestruct (fmlist_agree_1 with "Hexpected Hdata") as %->.

  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hf]").
  {
    iFrame "#∗".
    iNext.
    iExists _, _, _, _. iFrame "∗#%".
    iExists _, _. iFrame "∗#".
  }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
Qed.

End aof_proof.
