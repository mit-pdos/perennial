From Perennial.Helpers Require Import Map.
From iris.base_logic.lib Require Import mnat.
From Perennial.algebra Require Import auth_map liftable liftable2 log_heap async.

From Goose.github_com.mit_pdos.goose_nfsd Require Import buftxn.
From Perennial.program_logic Require Export ncinv.
From Perennial.program_proof Require Import buf.buf_proof addr.addr_proof txn.txn_proof.
From Perennial.program_proof Require buftxn.buftxn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_invariant.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.goose_lang.ffi Require Import disk_prelude.

Section goose_lang.
  Context `{!buftxnG Σ}.
  Context {N:namespace}.

  Implicit Types (l: loc) (γ: buftxn_names Σ) (γtxn: gname).
  Implicit Types (obj: object).

  Definition txn_init_ghost_state (logm_init: gmap addr object) γ : iProp Σ :=
    async_ctx γ.(buftxn_async_name) 1 {| latest := logm_init; pending := [] |}.

  (* NOTE(tej): we're combining the durable part with the resources into one
  definition here, unlike in lower layers (they should be fixed) *)
  Definition is_txn_durable γ dinit logm : iProp Σ :=
    is_txn_durable γ.(buftxn_txn_names) dinit ∗
    txn_resources γ.(buftxn_txn_names) logm ∗
    async_ctx γ.(buftxn_async_name) 1 logm.

  Definition txn_cfupd_cancel dinit k γ' : iProp Σ :=
    (<disc> (|C={⊤}_k=>
              ∃ logm', is_txn_durable γ' dinit logm' )).

  Definition crash_point γ logm crash_txn : iProp Σ :=
    (* TODO: wrap crash_txn in an agree, give out an exchanger ghost name for
    it *)
    async_ctx γ.(buftxn_async_name) 1 logm ∗
    ⌜(length (possible logm) = crash_txn + 1)%nat⌝.

  Definition txn_durable_exchanger γ txn_id :=
    heapspec.heapspec_durable_exchanger γ.(buftxn_txn_names).(txn_walnames) txn_id.

  Lemma txn_durable_exchanger_use γ n lb :
    txn_durable_exchanger γ n -∗
    txn_durable γ lb -∗
    ⌜ (lb ≤ n)%nat ⌝.
  Proof. iIntros. iApply (heapspec.heapspec_durable_exchanger_use with "[$] [$]"). Qed.

  Definition token_exchanger (a:addr) crash_txn γ γ' : iProp Σ :=
    (∃ i, async.own_last_frag γ.(buftxn_async_name) a i) ∨
    (async.own_last_frag γ'.(buftxn_async_name) a crash_txn ∗ modify_token γ' a).

  (* TODO: exchange
  [ephemeral_txn_val crash_txn γ a v]
  for
  [ephemeral_txn_val crash_txn γ' a v]
   *)
  Definition ephemeral_txn_val_exchanger (a:addr) crash_txn γ γ' : iProp Σ :=
    ∃ v, ephemeral_txn_val γ.(buftxn_async_name) crash_txn a v ∗
         ephemeral_txn_val γ'.(buftxn_async_name) crash_txn a v.

  Definition addr_exchangers {A} txn γ γ' (m : gmap addr A) : iProp Σ :=
    ([∗ map] a↦_ ∈ m,
        token_exchanger a txn γ γ' ∗
        ephemeral_txn_val_exchanger a txn γ γ')%I.

  Definition sep_txn_exchanger γ γ' : iProp Σ :=
    ∃ logm crash_txn,
       "Hcrash_point" ∷ crash_point γ logm crash_txn ∗
       "Hdurable_exchanger" ∷ txn_durable_exchanger γ crash_txn ∗
       "#Hcrash_txn_durable" ∷ txn_durable γ' crash_txn ∗
       "Hexchanger" ∷ addr_exchangers crash_txn γ γ' (latest logm)
  .

  Lemma exchange_big_sepM_addrs γ γ' (m0 m1 : gmap addr object) crash_txn :
    dom (gset _) m0 ⊆ dom (gset _) m1 →
    txn_durable γ' crash_txn -∗
    addr_exchangers crash_txn γ γ' m1 -∗
    ([∗ map] k0↦x ∈ m0, ephemeral_txn_val γ.(buftxn_async_name) crash_txn k0 x ∗
                        (∃ i v, ephemeral_val_from γ.(buftxn_async_name) i k0 v)) -∗
    addr_exchangers crash_txn γ γ' m1 ∗
    [∗ map] k0↦x ∈ m0, durable_mapsto_own γ' k0 x.
  Proof.
    iIntros (Hdom) "#Hdur H1 H2".
    rewrite /addr_exchangers.
    iCombine "Hdur H1" as "H1".
    iDestruct (big_sepM_mono_with_inv with "H1 H2") as "((_&$)&H)"; last iApply "H".
    iIntros (k o Hlookup) "((#Hdur&Hm)&Hephem)".
    assert (is_Some (m1 !! k)) as (v&?).
    { apply elem_of_dom, Hdom, elem_of_dom. eauto. }
    iDestruct (big_sepM_lookup_acc with "Hm") as "(H&Hm)"; first eassumption.
    iDestruct "Hephem" as "(#Hval0&Hephem)".
    iDestruct "Hephem" as (??) "(_&Htok0)".
    iDestruct "H" as "(Htok&#Hval)".
    iDestruct "Hval" as (?) "(Hval1&Hval2)".
    iDestruct (ephemeral_txn_val_agree with "Hval0 Hval1") as %Heq. subst.
    iDestruct "Htok" as "[Hl|(Hr1&Hr2)]".
    { iExFalso. iDestruct "Hl" as (?) "H".
      iApply (own_last_frag_conflict with "[$] [$]"). }
    iSpecialize ("Hm" with "[Htok0]").
    { iSplitL "Htok0".
      - iLeft. eauto.
      - iExists _. iFrame "#". }
    iFrame "# ∗". iExists _. iFrame "# ∗".
  Qed.

  Definition txn_cinv γ γ' : iProp Σ :=
    □ |C={⊤}_0=> inv (N.@"txn") (sep_txn_exchanger γ γ').

  Lemma exchange_mapsto_commit γ γ' m0 m txn_id k :
    dom (gset _) m0 ⊆ dom (gset _) m →
    ("#Htxn_cinv" ∷ txn_cinv γ γ' ∗
    "Hold_vals" ∷ ([∗ map] k↦x ∈ m0,
          ∃ i : nat, txn_durable γ i ∗
                     ephemeral_txn_val_range γ.(buftxn_async_name) i txn_id k x) ∗
    "Hval" ∷ [∗ map] k↦x ∈ m, ephemeral_val_from γ.(buftxn_async_name) txn_id k x) -∗
    |C={⊤}_S k => ([∗ map] a↦v ∈ m0, durable_mapsto_own γ' a v) ∨
                  ([∗ map] a↦v ∈ m, durable_mapsto_own γ' a v).
  Proof.
    iIntros (Hdom1) "H". iNamed "H".
    iMod ("Htxn_cinv") as "#Hinv"; first lia.
    iIntros "HC".
    iInv ("Hinv") as ">H" "Hclo".
    iNamed "H".
    iDestruct "Hcrash_point" as "(Hasync&%Heq)".
    iAssert (⌜dom (gset addr) m ⊆ dom (gset addr) logm.(latest)⌝)%I with "[Hval Hasync]" as "%Hdom2".
    {
      clear Hdom1.
      iInduction m as [| i x m] "IH" using map_ind.
      { iPureIntro; set_solver. }
      rewrite big_sepM_insert //.
      iDestruct "Hval" as "(Hval1&Hval)".
      iDestruct ("IH" with "[$] [$]") as %Hdom.
      iDestruct (ephemeral_val_from_agree_latest with "[$] [$]") as %Hlookup.
      iPureIntro. rewrite dom_insert.
      assert (i ∈ dom (gset addr) (logm.(latest))).
      { apply elem_of_dom. eauto. }
      set_solver.
    }

    destruct (decide (crash_txn < txn_id)).
    - (* We roll back, txn_id is not durable *)
      iAssert (txn_durable_exchanger γ crash_txn ∗
               ([∗ map] k0↦x ∈ m0, ephemeral_txn_val γ.(buftxn_async_name) crash_txn k0 x))%I
        with "[Hold_vals Hdurable_exchanger]" as "(Hdurable_exchanger&#Hold)".
      {
        iDestruct (big_sepM_mono_with_inv with "Hdurable_exchanger Hold_vals") as "($&H)"; last iApply "H".
        iIntros (?? Hlookup) "(Hdurable_exchanger&H)".
        iDestruct "H" as (i) "(Hdurable&Hrange)".
        iDestruct (txn_durable_exchanger_use with "[$] [$]") as %Hlb.
        iFrame. iApply (ephemeral_txn_val_range_acc with "[$]").
        lia.
      }
      iAssert ([∗ map] k0↦_ ∈ m, ∃ txn_id x, ephemeral_val_from γ.(buftxn_async_name) txn_id k0 x)%I
       with "[Hval]" as "Hval".
      { iApply (big_sepM_mono with "Hval"); eauto. }
      iDestruct (big_sepM_dom with "Hval") as "Hval".
      iDestruct (big_sepS_subseteq with "Hval") as "Hval"; eauto.
      iDestruct (big_sepM_dom with "Hval") as "Hval".
      iCombine "Hold Hval" as "Hval".
      iEval (rewrite -big_sepM_sep) in "Hval".
      iDestruct (exchange_big_sepM_addrs with "[$] [$] Hval") as "(Hexchanger&Hval)".
      { etransitivity; last eassumption; eauto. }
      iMod ("Hclo" with "[Hexchanger Hdurable_exchanger Hasync]").
      { iNext. iExists _, _. iFrame "# ∗". eauto. }
      iModIntro. eauto.
    - (* We go forward, txn_id is durable *)
      iAssert (async_ctx γ.(buftxn_async_name) 1 logm ∗
                ([∗ map] k0↦x ∈ m, ephemeral_txn_val γ.(buftxn_async_name) crash_txn k0 x
                    ∗ (∃ (i : nat) (v : object), ephemeral_val_from γ.(buftxn_async_name) i k0 v)))%I
              with "[Hasync Hval]" as "[Hasync Hval]".
      {iDestruct (big_sepM_mono_with_inv with "Hasync Hval") as "($&H)"; last iApply "H".
       iIntros (? ? Hlookup) "(Hasync&Hval)".
       iDestruct (ephemeral_val_from_val with "Hasync Hval") as "#$".
       { lia. }
       { lia. }
       iFrame. iExists _, _; eauto.
      }
      iDestruct (exchange_big_sepM_addrs with "[$] [$] Hval") as "(Hexchanger&Hval)".
      { eauto. }
      iMod ("Hclo" with "[Hexchanger Hdurable_exchanger Hasync]").
      { iNext. iExists _, _. iFrame "# ∗". eauto. }
      iModIntro. eauto.
  Qed.


  Theorem wpc_MkTxn (d:loc) γ dinit logm k :
    {{{ is_txn_durable γ dinit logm }}}
      txn.MkTxn #d @ k; ⊤
    {{{ γ' (l: loc), RET #l;
        is_txn l γ.(buftxn_txn_names) dinit ∗
        is_txn_system N γ ∗
        txn_cfupd_cancel dinit k γ' ∗
        txn_cinv γ γ' }}}
    {{{ ∃ γ' logm', ⌜ γ'.(buftxn_txn_names).(txn_kinds) = γ.(buftxn_txn_names).(txn_kinds) ⌝ ∗
                   is_txn_durable γ' dinit logm' }}}.
  Proof.
  Abort.

End goose_lang.
