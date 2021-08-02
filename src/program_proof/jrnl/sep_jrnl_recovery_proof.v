From Perennial.Helpers Require Import Map.
From Perennial.algebra Require Import auth_map liftable log_heap async.

From Goose.github_com.mit_pdos.go_journal Require Import jrnl.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof obj.obj_proof.
From Perennial.program_proof Require jrnl.jrnl_proof.
From Perennial.program_proof Require Import jrnl.sep_jrnl_invariant.
From Perennial.program_proof Require Import disk_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

From RecordUpdate Require Import RecordUpdate.
Import RecordSetNotations.

Section goose_lang.
  Context `{!jrnlG Σ}.
  Context `{!heapGS Σ}.
  Context (N:namespace).
  Context (Hdisj1: (↑N : coPset) ## ↑invN).
  Context (Hdisj2: (↑N : coPset) ## ↑invariant.walN).

  Implicit Types (l: loc) (γ: jrnl_names) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_init_ghost_state γ : iProp Σ :=
    async_pre_ctx γ.(jrnl_async_name).

  (* NOTE(tej): we're combining the durable part with the resources into one
  definition here, unlike in lower layers (they should be fixed) *)
  Definition is_txn_durable γ dinit logm : iProp Σ :=
    "Hlower_durable" ∷ is_txn_durable γ.(jrnl_txn_names) dinit ∗
    "Hlogm" ∷ ghost_var γ.(jrnl_txn_names).(txn_crashstates) (3/4) logm ∗
    "Hasync_ctx" ∷ async_ctx γ.(jrnl_async_name) 1 logm.

  Lemma is_txn_durable_init dinit (kinds: gmap u64 bufDataKind) (sz: nat) :
    dom (gset _) dinit = list_to_set (seqZ 513 sz) →
    dom (gset _) kinds = list_to_set (U64 <$> (seqZ 513 sz)) →
    (513 + Z.of_nat sz) * block_bytes * 8 < 2^64 →
    0 d↦∗ repeat block0 513 ∗ 513 d↦∗ repeat block0 sz -∗
  |==> ∃ γ, let logm0 := Build_async (kind_heap0 kinds) [] in
            ⌜ γ.(jrnl_txn_names).(txn_kinds) = kinds ⌝ ∗
              is_txn_durable γ dinit logm0 ∗
              txn_durable γ 0 ∗
              ([∗ map] a ↦ o ∈ kind_heap0 kinds, durable_mapsto_own γ a o)
  .
  Proof.
    iIntros (Hdom1 Hdom2 Hlt) "Hpre".

    set (logm0 := Build_async (kind_heap0 kinds) []).

    iMod (recovery_proof.is_txn_durable_init dinit kinds with "Hpre") as
        (γtxn) "Htxn"; [ done .. | iNamed "Htxn" ].
    iMod (async_pre_ctx_init) as (γasync) "Hctx".
    iMod (async_ctx_init _ logm0 with "Hctx") as "[Hctx Hephemeral_val_froms]".
    { simpl. apply Forall_nil; auto. }
    simpl.

    iModIntro.
    iExists {| jrnl_txn_names := γtxn;
               jrnl_async_name := γasync; |}.
    rewrite /is_txn_durable /=.
    (* TODO: iFrame here is way slower than it should be, if Htxn_durable isn't
    specified first *)
    iFrame "Htxn_durable ∗".
    iFrame "Hdurable_lb".
    iDestruct (big_sepM_sep with "[$Hmapsto_txns $Hephemeral_val_froms]") as "H".
    iSplit; first eauto.
    iApply (big_sepM_impl with "H"); simpl.
    iIntros "!>" (a o Hlookup) "[Hmapsto Heph]".
    rewrite /durable_mapsto_own.
    iSplitL "Hmapsto".
    - iExists _; iFrame.
    - rewrite /durable_mapsto /=.
      iExists _; iFrame.
      rewrite /txn_durable /=.
      iFrame "#".
  Qed.

  Definition txn_cfupd_cancel dinit γ' : iProp Σ :=
    (<bdisc> (|C={⊤}_0=>
              ▷ ∃ logm', is_txn_durable γ' dinit logm' )).


  Lemma sep_txn_crash_transform γ σs γasync' γtxn_names' dinit :
    "H◯async" ∷ ghost_var γ.(jrnl_txn_names).(txn_crashstates) (3 / 4) σs ∗
    "H●latest" ∷ async_ctx γ.(jrnl_async_name) 1 σs ∗
    "Hctx" ∷ async_pre_ctx γasync' ∗
    "H" ∷ (∃ logm0 : async (gmap addr object), txn_resources γ.(jrnl_txn_names) γtxn_names' logm0) ∗
    "Hcancel" ∷ recovery_proof.is_txn_durable γtxn_names' dinit ==∗
    let γ' := {| jrnl_txn_names := γtxn_names'; jrnl_async_name := γasync' |} in
     sep_txn_exchanger γ γ' ∗ (∃ logm' : async (gmap addr object), is_txn_durable γ' dinit logm').
  Proof.
    iNamed 1.
    iNamed "H".
    iDestruct (ghost_var_agree with "Holdlogm [$]") as %<-.
    iMod (async_ctx_init_set_prefix _ _ _ _ logm0 with "H●latest Hctx") as "(H●latest&Hctx'&Hephem)".
    { eauto. }
    iModIntro.
    iDestruct (async_ctx_doms_prefix_latest _ _ logm0 logm1 with "[$]") as %Hdom.
    { auto. }
    iSplitL "Hdurable_exchanger Hdurable Hmapsto_txns Hephem H●latest".
    {
      iExists logm1, txn_id. iFrame.
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
    iExists _. simpl.  iFrame "Hctx' Hlogm Hcancel".
  Qed.

  Theorem wpc_MkLog d γ dinit logm k :
    {{{ is_txn_durable γ dinit logm }}}
      obj.MkLog (disk_val d) @ k; ⊤
    {{{ γ' (l: loc), RET #l;
        is_txn l γ.(jrnl_txn_names) dinit ∗
        is_txn_system N γ ∗
        txn_cfupd_cancel dinit γ' ∗
        txn_cinv N γ γ' }}}
    {{{ ∃ γ' logm',
        is_txn_durable γ' dinit logm' ∗
       (⌜ γ' = γ ⌝ ∨ (* sep_txn_exchanger γ γ' *)
        txn_cinv N γ γ') }}}.
  Proof using Hdisj1 Hdisj2.
    iIntros (Φ Φc) "H HΦ".
    rewrite /is_txn_durable.
    iNamed "H".
    iApply wpc_cfupd.
    iApply wpc_ncfupd.
    wpc_apply (recovery_proof.wpc_MkLog (↑invariant.walN ∪ ↑invN) with "[$Hlower_durable]").
    3: {
      iSplit.
      - iLeft in "HΦ".
        iIntros "H". iDestruct "H" as (?? Heq) "(Hlower_durable&[%Heq2|Hres])".
        { rewrite Heq2. iModIntro. iApply "HΦ". iExists γ, _. iFrame. eauto. }
        iRename "Hlogm" into "Holdlogm1".
        iIntros "HC".
        iMod (async_pre_ctx_init) as (γasync') "Hasync_ctx'".
        iMod (sep_txn_crash_transform γ with "[$Holdlogm1 $Hasync_ctx $Hasync_ctx' $Hlower_durable Hres]")
          as "(H1&H2)".
        { eauto. }

        iApply "HΦ".
        iDestruct "H2" as (logm'') "H2".
        iExists {| jrnl_txn_names := γ'; jrnl_async_name := γasync' |}, logm''.
        iMod (inv_alloc' with "H1") as "#Hinv".
        iModIntro.
        iFrame "H2".
        iRight.
        iSplit; last by auto.
        do 2 iModIntro.
        iFrame "Hinv".
      - iNext. iIntros (γtxn_names' l) "(#Histxn&Hcancel&Hmapstos)".
        iRight in "HΦ".
        rewrite /txn_cfupd_res.
        iDestruct "Hmapstos" as "[%Heq_kinds Hmapstos]".
        iDestruct (own_discrete_laterable with "Hmapstos") as (Ptxn_tok) "(HPtxn_tok&#HPtxn_tok_wand)".
        iDestruct (own_discrete_laterable with "Hcancel") as
            (Ptxn_cancel_tok) "(HPtxn_cancel_tok&#HPtxn_cancel_tok_wand)".


        iMod (async_pre_ctx_init) as (γasync') "Hasync_init_ctx'".
        iDestruct (async_ctx_to_lb with "Hasync_ctx") as "#Hasync_lb".
        set (γ' := {| jrnl_txn_names := γtxn_names'; jrnl_async_name := γasync' |}).
        iMod (ncinv_cinv_alloc N _ _ ⊤
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
          iMod (fupd_mask_mono with "H") as ">H".
          { set_solver. }
          iDestruct ("HPtxn_cancel_tok_wand" with "[$]") as ">Hcancel".
          iSpecialize ("Hcancel" with "[$]").
          iMod (fupd_mask_mono with "Hcancel") as ">Hcancel".
          { set_solver. }
          iMod (sep_txn_crash_transform with "[$]") as "($&$)".
          eauto.
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
        auto.
    }
    { set_solver+. }
    { set_solver+. }
    Unshelve.
    exact O. (* This will almost certainly go away when we remove the useless k subscript on wpc *)
  Qed.

End goose_lang.
