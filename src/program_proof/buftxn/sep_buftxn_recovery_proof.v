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

  Definition txn_init_ghost_state (logm_init: gmap addr object) γ : iProp Σ :=
    async_ctx γ.(buftxn_async_name) 1 {| latest := logm_init; pending := [] |}.

  (* NOTE(tej): we're combining the durable part with the resources into one
  definition here, unlike in lower layers (they should be fixed) *)
  Definition is_txn_durable γ dinit logm : iProp Σ :=
    "Hlower_durable" ∷ is_txn_durable γ.(buftxn_txn_names) dinit ∗
    "Hlogm" ∷ ghost_var γ.(buftxn_txn_names).(txn_crashstates) (3/4) logm ∗
    "Hasync_ctx" ∷ async_ctx γ.(buftxn_async_name) 1 logm.

  Definition txn_cfupd_cancel dinit k γ' : iProp Σ :=
    (<bdisc> (|C={⊤}_k=>
              ∃ logm', is_txn_durable γ' dinit logm' )).


  Theorem wpc_MkTxn (d:loc) γ dinit logm k :
    {{{ is_txn_durable γ dinit logm }}}
      txn.MkTxn #d @ k; ⊤
    {{{ γ' (l: loc), RET #l;
        is_txn l γ.(buftxn_txn_names) dinit ∗
        is_txn_system N γ ∗
        txn_cfupd_cancel dinit k γ' ∗
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
        iMod (async_ctx_init logm') as (γasync') "Hasync_ctx'".
        iIntros "HC !>".
        iApply "HΦ".
        iExists {| buftxn_txn_names := γ'; buftxn_async_name := γasync' |}, _.
        iFrame "Hlower_durable  Hasync_ctx'".
        iClear "Hlogm".
        iNamed "Hres". iFrame. eauto.
      - iNext. iIntros (γtxn_names' l) "(#Histxn&Hcancel&Hmapstos)".
        iRight in "HΦ".
        rewrite /txn_cfupd_res.
        iDestruct (own_discrete_laterable with "Hmapstos") as (Ptxn_tok) "(HPtxn_tok&#HPtxn_tok_wand)".
        iMod (async_ctx_init (Build_async (∅ : gmap addr object) [])) as (γasync') "Hasync_ctx'".
        set (γ' := {| buftxn_txn_names := γtxn_names'; buftxn_async_name := γasync' |}).
        iMod (ncinv_cinv_alloc' N _ ⊤
                (txn_system_inv γ ∗ async_ctx γasync' 1 {| latest := ∅; pending := [] |} ∗ Ptxn_tok)
                (sep_txn_exchanger γ γ')
                (∃ logm', is_txn_durable γ' dinit logm')%I
          with "[] [Hlogm Hasync_ctx' HPtxn_tok Hasync_ctx]") as "(#Htxn_inv&Hcfupd)".
        { set_solver. }
        {
          iModIntro. iIntros "(>Hinv&>Hctx&HPtxn_tok) HC".
          iNamed "Hinv".
          iDestruct ("HPtxn_tok_wand" with "[$]") as ">H".
          iSpecialize ("H" with "[$]").
          iMod (fupd_level_mask_mono with "H") as ">H".
          { set_solver. }
          iNamed "H".
          iAssert (|==> async_ctx γasync' 1 logm0 ∗
                        ([∗ map] k↦v ∈ latest logm0, ephemeral_val_from γasync' (length (possible logm0) - 1) k v)
                        )%I with "[Hctx]" as ">(Hctx&Hephem)".
          { admit. }
          iModIntro.
          iDestruct (ghost_var_agree with "Holdlogm [$]") as %<-.
          iSplitL "Hdurable_exchanger Hdurable Hmapsto_txns Hephem H●latest".
          {
            iNext. iExists logm1, txn_id. iFrame.
            iSplitL "".
            { iPureIntro. lia. }
            iCombine "Hmapsto_txns Hephem" as "Hpts".
            rewrite -big_sepM_sep.
            rewrite /addr_exchangers.

            (* TODO: need to know logm0 and logm1 have the same domain, but
               where will this ocme from?  if async_ctx maintains that every map
               has same domain, then we can use the logm0 is a prefix of loogm1
               (that can be provided by txn_recovery *)

            (* TODO: need to regenerate the old txn vals, but we have the ctx *)
            assert (dom (gset _) logm1.(latest) = dom (gset _) logm0.(latest)) as Hdom.
            { admit. }
            iApply big_sepM_dom. rewrite Hdom. iApply big_sepM_dom.
            iApply (big_sepM_mono with "Hpts").
            {
              iIntros (?? Hlookup) "(Hmapsto&Hval)".
              iDestruct "Hval" as "(#Hval&Htok)".
              iSplitL "Hmapsto Htok".
              { rewrite /token_exchanger.
                iRight. iSplitL "Htok".
                { iExactEq "Htok". f_equal. lia. }
                { iExists _. iFrame. }
              }
              iExists _.
              iSplitR "Hval".
              { admit. }
              { iExactEq "Hval". f_equal. lia. }
            }
          }
          rewrite /is_txn_durable.
          iNext. iExists _. simpl. iFrame "Hctx Hlogm".
          admit.
        }
        {
        iFrame. iNext. rewrite /txn_system_inv. iExists _. iFrame.
        }
        admit.
    }
    { set_solver+. }
    { set_solver+. }
  Admitted.

End goose_lang.
