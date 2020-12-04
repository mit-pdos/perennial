From Perennial.Helpers Require Import Map.
From iris.base_logic.lib Require Import mnat.
From Perennial.algebra Require Import auth_map liftable log_heap async.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_invariant.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Section goose_lang.
  Context `{!buftxnG Σ}.
  Context {N:namespace}.
  Context (Hdisj1: (↑N : coPset) ## ↑invN).
  Context (Hdisj2: (↑N : coPset) ## ↑invariant.walN).

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_init_ghost_state γ : iProp Σ :=
    async_pre_ctx γ.(buftxn_async_name).

  (* NOTE(tej): we're combining the durable part with the resources into one
  definition here, unlike in lower layers (they should be fixed) *)
  Definition is_txn_durable γ dinit logm : iProp Σ :=
    "Hlower_durable" ∷ is_txn_durable γ.(buftxn_txn_names) dinit ∗
    "Hlogm" ∷ ghost_var γ.(buftxn_txn_names).(txn_crashstates) (3/4) logm ∗
    "Hasync_ctx" ∷ async_ctx γ.(buftxn_async_name) 1 logm.

  Definition txn_cfupd_cancel dinit γ' : iProp Σ :=
    (<bdisc> (|C={⊤}_0=>
              ▷ ∃ logm', is_txn_durable γ' dinit logm' )).


  Theorem wpc_MkTxn (d:loc) γ dinit logm k :
    {{{ is_txn_durable γ dinit logm }}}
      txn.MkTxn #d @ k; ⊤
    {{{ γ' (l: loc), RET #l;
        is_txn l γ.(buftxn_txn_names) dinit ∗
        is_txn_system N γ ∗
        txn_cfupd_cancel dinit γ' ∗
        txn_cinv N γ γ' }}}
    {{{ ∃ γ' logm', ⌜ γ'.(buftxn_txn_names).(txn_kinds) = γ.(buftxn_txn_names).(txn_kinds) ⌝ ∗
                   is_txn_durable γ' dinit logm' }}}.
  Proof.
    iIntros (Φ Φc) "H HΦ".
    rewrite /is_txn_durable.
    iNamed "H".
    iApply wpc_cfupd.
    iApply wpc_ncfupd.
    wpc_apply (recovery_proof.wpc_MkTxn (↑invariant.walN ∪ ↑invN) with "[$Hlower_durable]").
    3: {
      iSplit.
      - iLeft in "HΦ". iModIntro.
        iIntros "H". iDestruct "H" as (?? Heq) "(Hlower_durable&[%Heq2|Hres])".
        { rewrite Heq2. iModIntro. iApply "HΦ". iExists γ, _. iFrame. eauto. }
        iRename "Hlogm" into "Holdlogm1".
        iNamed "Hres".
        iDestruct (ghost_var_agree with "Holdlogm1 [$]") as %<-.
        iIntros "HC".
        iMod (async_pre_ctx_init) as (γasync') "Hasync_ctx'".
        iMod (async_ctx_init_set_prefix _ _ _ logm logm' with "Hasync_ctx [$]")
          as "(Hasync_ctx&Hasync_ctx'&Hpts)".
        { eauto. }
        iIntros "!>".
        iApply "HΦ".
        iExists {| buftxn_txn_names := γ'; buftxn_async_name := γasync' |}, _.
        iFrame "Hlower_durable  Hasync_ctx'". iFrame. eauto.
      - iNext. iIntros (γtxn_names' l) "(#Histxn&Hcancel&Hmapstos)".
        iRight in "HΦ".
        rewrite /txn_cfupd_res.
        iDestruct (own_discrete_laterable with "Hmapstos") as (Ptxn_tok) "(HPtxn_tok&#HPtxn_tok_wand)".
        iDestruct (own_discrete_laterable with "Hcancel") as
            (Ptxn_cancel_tok) "(HPtxn_cancel_tok&#HPtxn_cancel_tok_wand)".


        iMod (async_pre_ctx_init) as (γasync') "Hasync_init_ctx'".
        iDestruct (async_ctx_to_lb with "Hasync_ctx") as "#Hasync_lb".
        set (γ' := {| buftxn_txn_names := γtxn_names'; buftxn_async_name := γasync' |}).
        iMod (ncinv_cinv_alloc N _ ⊤
                (txn_system_inv γ ∗ (async_pre_ctx γasync' ∗ Ptxn_tok ∗ Ptxn_cancel_tok))
                (sep_txn_exchanger γ γ')
                (∃ logm', is_txn_durable γ' dinit logm')%I
          with "[] [Hlogm Hasync_init_ctx' HPtxn_tok HPtxn_cancel_tok Hasync_ctx]") as "(#Htxn_inv&Hcfupd)".
        { set_solver. }
        {
          iModIntro. iIntros "(>Hinv&>Hctx&HPtxn_tok&HPtxn_cancel_tok) #HC".
          iNamed "Hinv".
          iDestruct ("HPtxn_tok_wand" with "[$]") as ">H".
          iSpecialize ("H" with "[$]").
          iMod (fupd_level_mask_mono with "H") as ">H".
          { set_solver. }
          iNamed "H".
          iDestruct ("HPtxn_cancel_tok_wand" with "[$]") as ">Hcancel".
          iSpecialize ("Hcancel" with "[$]").
          iMod (fupd_level_mask_mono with "Hcancel") as ">Hcancel".
          { set_solver. }
          iDestruct (ghost_var_agree with "Holdlogm [$]") as %<-.
          iMod (async_ctx_init_set_prefix _ _ _ _ logm0 with "H●latest Hctx") as "(H●latest&Hctx'&Hephem)".
          { eauto. }
          iModIntro.
          iDestruct (async_ctx_doms_prefix_latest _ _ logm0 logm1 with "[$]") as %Hdom.
          { auto. }
          iSplitL "Hdurable_exchanger Hdurable Hmapsto_txns Hephem H●latest".
          {
            iNext. iExists logm1, txn_id. iFrame.
            iSplitL "".
            { iPureIntro. lia. }
            iCombine "Hmapsto_txns Hephem" as "Hpts".
            rewrite -big_sepM_sep.
            rewrite /addr_exchangers.

            iApply big_sepM_dom. rewrite -Hdom. iApply big_sepM_dom.
            iApply (big_sepM_mono with "Hpts").
            {
              iIntros (?? Hlookup) "(Hmapsto&#Hval1&Hval_from)".
              iDestruct "Hval_from" as "(#Hval2&Htok)".
              iSplitL "Hmapsto Htok".
              { rewrite /token_exchanger.
                iRight. iSplitL "Htok".
                { iExactEq "Htok". f_equal. lia. }
                { iExists _. iFrame. }
              }
              iExists _.
              iSplit.
              { iExactEq "Hval1". f_equal. lia. }
              { iExactEq "Hval2". f_equal. lia. }
            }
          }
          rewrite /is_txn_durable.
          iNext. iExists _. simpl.  iFrame "Hctx' Hlogm Hcancel".
        }
        {
        iFrame. iNext. rewrite /txn_system_inv. iExists _. iFrame.
        }
        iDestruct "Hcfupd" as "(Hcfupd1&Hcfupd2)".
        iModIntro. iApply "HΦ".
        iFrame "#".
        iSplitL "".
        { rewrite /is_txn_system. rewrite /is_txn. iNamed "Histxn". iFrame "#".
          iApply (ncinv_split_l). iApply "Htxn_inv".
        }
        rewrite /txn_cfupd_cancel.
        rewrite /txn_cinv.
        iFrame.
    }
    { set_solver+. }
    { set_solver+. }
  Qed.

End goose_lang.
