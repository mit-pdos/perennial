From Perennial.goose_lang Require Import lang notation typing.
From Perennial.goose_lang.lib Require Import map.impl list.impl list.list_slice.
From Perennial.goose_lang.ffi Require Import jrnl_ffi.
From Perennial.goose_lang.ffi Require Import disk.
From Goose.github_com.mit_pdos.goose_nfsd Require Import txn twophase.
From Perennial.program_proof Require Import lockmap_proof.
From Perennial.program_proof Require Import twophase.op_wrappers.
From Perennial.program_proof Require Import addr.addr_proof buf.buf_proof txn.txn_proof.
From Perennial.program_proof Require Import buftxn.sep_buftxn_proof.
From Perennial.program_proof Require Import twophase.twophase_proof.
From Perennial.goose_lang.lib.list Require Import list.
From Perennial.goose_lang Require Import spec_assert.

From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.program_proof Require Import proof_prelude.

Section proof.
  Context `{!buftxnG Σ}.
  Context `{!heapG Σ}.
  Context `{!lockmapG Σ}.
  Existing Instances jrnl_spec_ext jrnl_spec_ffi_model jrnl_spec_ext_semantics jrnl_spec_ffi_interp
           jrnl_spec_interp_adequacy.
  Context `{!refinement_heapG Σ}.
  Context `{!jrnlG Σ}.

  Implicit Types (N: namespace).

  Definition is_twophase_system N γ :=
    is_txn_system N γ.

  Definition val_of_obj (o : obj) := val_of_list ((λ u, LitV (LitByte u)) <$> o).

  Definition jrnl_mapsto_own addr obj : iProp Σ :=
    ∃ obj', jrnl_mapsto addr 1 obj' ∗ ⌜data_has_obj obj' addr obj⌝.

  Definition jrnl_maps_have_mt_changed (σj1 σj2: jrnl_map) (mt_changed: gmap addr versioned_object) :=
    dom (gset addr) (jrnlData σj1) = dom (gset addr) (jrnlData σj2) ∧
    map_Forall (λ addr vobj,
      match mt_changed !! addr with
      | Some vobj' =>
        data_has_obj vobj.1 addr (committed vobj') ∧
        data_has_obj vobj.2 addr (modified vobj')
      | None => vobj.1 = vobj.2
      end
    ) (map_zip (jrnlData σj1) (jrnlData σj2)).

  Definition is_twophase_pre l (γ γ' : buftxn_names) dinit (objs_dom: gset addr) : iProp Σ :=
    ∃ (txnl locksl : loc) ghs,
      "#Hpre.txn" ∷ readonly (l ↦[TwoPhasePre.S :: "txn"] #txnl) ∗
      "#Hpre.locks" ∷ readonly (l ↦[TwoPhasePre.S :: "locks"] #locksl) ∗
      "#Histxn_system" ∷ is_txn_system Nbuftxn γ ∗
      "#Histxn" ∷ is_txn txnl γ.(buftxn_txn_names) dinit ∗
      "#HlockMap" ∷ is_lockMap locksl ghs (set_map addr2flat objs_dom)
        (twophase_linv_flat 0 jrnl_mapsto_own γ) ∗
      "#Htxn_cinv" ∷ txn_cinv Nbuftxn γ γ' ∗
      "%Hvalids" ∷ ⌜set_Forall valid_addr objs_dom⌝.

  Definition is_twophase_started l γ dinit objs_dom j K e1 e2 : iProp Σ :=
    ∃ σj1 σj2 mt_changed ls,
      (* mark: do we need is_twophase_pre in here too? *)
      "Hj" ∷ j ⤇ K (Atomically ls e1) ∗
      "Htwophase" ∷ is_twophase_raw
        l γ dinit 0 jrnl_mapsto_own objs_dom mt_changed ∗
      "%Halways_steps" ∷ ⌜ always_steps e1 σj1 e2 σj2 ⌝ ∗
      "%Hmt_changed" ∷ ⌜ jrnl_maps_have_mt_changed σj1 σj2 mt_changed ⌝.

  Definition is_twophase_releasable l γ (objs_dom: gset addr) : iProp Σ :=
    ∃ locks_held mt_changed σj1 σj2,
      (* mark: do we need is_twophase_pre in here too? *)
      "Hlocks" ∷ is_twophase_locks
        l γ 0 jrnl_mapsto_own (set_map addr2flat objs_dom) locks_held ∗
      "Hlinvs" ∷ ([∗ list] flat_a ∈ locks_held, (
        "Hlinv" ∷ twophase_linv_flat 0 jrnl_mapsto_own γ flat_a
      )) ∗
      "%Hlocks_held" ∷ ⌜
        set_map addr2flat (dom (gset addr) mt_changed) =
        (list_to_set locks_held: gset u64)
      ⌝ ∗
      "%Hmt_changed" ∷ ⌜ jrnl_maps_have_mt_changed σj1 σj2 mt_changed ⌝ ∗
      "%Hvalids" ∷ ⌜set_Forall valid_addr objs_dom⌝.

  Theorem wpc_Init N (d: loc) γ dinit logm mt k :
    N ## invN →
    N ## invariant.walN →
    map_Forall (mapsto_valid γ) mt →
    {{{
      "Htxn_durable" ∷ is_txn_durable γ dinit logm ∗
      "Hmapstos" ∷ ([∗ map] a ↦ obj ∈ mt,
        "Hdurable_mapsto" ∷ durable_mapsto_own γ a obj ∗
        "Hjrnl_mapsto" ∷ jrnl_mapsto_own a obj
      )
    }}}
      Init #d @ k; ⊤
    {{{
      γ' (l: loc), RET #l;
      "Htwophase" ∷ is_twophase_pre
        l γ γ' dinit (dom (gset addr) mt)
    }}}
    {{{ ∃ γ' logm',
      is_txn_durable γ' dinit logm' ∗
      (⌜ γ' = γ ⌝ ∨ txn_cinv Nbuftxn γ γ')
    }}}.
  Proof.
    iIntros (HinvN HwalN Hvalids Φ Φc) "(?&?) HΦ".
    iNamed.
    wpc_call.
    {
      iExists _, _.
      iFrame.
      auto.
    }
    wpc_apply (wpc_MkTxn Nbuftxn with "Htxn_durable").
    1-2: solve_ndisj.
    iSplit.
    {
      iDestruct "HΦ" as "[HΦ _]".
      iFrame.
    }
    iModIntro.
    iIntros (? txnl) "
      (#Histxn&#Histxn_system&Htxn_cancel&#Htxn_cinv&%Htxn_kinds)
    ".
    iApply wpc_cfupd.
    iCache with "HΦ Htxn_cancel".
    {
      iDestruct "HΦ" as "[HΦ _]".
      iModIntro.
      iMod "Htxn_cancel"; first by lia.
      iMod "Htxn_cancel".
      iDestruct "Htxn_cancel" as (?) "Htxn_cancel".
      iModIntro.
      iApply "HΦ".
      iExists _, _.
      iFrame "∗ #".
      auto.
    }
    wpc_frame.
    iMod (twophase_init_locks with "Histxn_system Hmapstos") as "?".
    1-2: set_solver.
    {
      intros a Hin.
      apply elem_of_dom in Hin.
      destruct Hin as [obj Hacc].
      apply Hvalids in Hacc.
      destruct Hacc as (Hvalid&_&_).
      assumption.
    }
    iNamed.
    wp_apply (
      wp_MkLockMap _ (twophase_linv_flat 0 jrnl_mapsto_own γ)
      with "[Hlinvs]"
    ).
    {
      iApply (big_sepS_impl with "Hlinvs").
      iIntros (addr_flat) "!> %Hin $".
    }
    iIntros (locksl ?) "#Hlocks".
    wp_apply wp_allocStruct; first by auto.
    iIntros (prel) "Hprel".
    iDestruct (struct_fields_split with "Hprel") as "(?&?&_)".
    iNamed.
    iMod (readonly_alloc_1 with "txn") as "#Hpre.txn".
    iMod (readonly_alloc_1 with "locks") as "#Hpre.locks".
    wp_pures.
    iIntros "[? ?]".
    iNamed.

    iApply "HΦ".
    iExists _, _, _.
    iFrame (Htxn_kinds) "#".
    iPureIntro.
    intros addr Hin.
    apply elem_of_dom in Hin.
    destruct Hin as [obj Hacc].
    apply Hvalids in Hacc.
    destruct Hacc as (Hvalid&_&_).
    assumption.
  Qed.

  Theorem wp_TwoPhase__Begin' N prel γ γ' dinit objs_dom j K ls e1 :
    {{{
      "Htwophase" ∷ is_twophase_pre prel γ γ' dinit objs_dom ∗
      "Hatom" ∷ j ⤇ K (Atomically ls e1)
    }}}
      Begin #prel
    {{{ tphl, RET #tphl;
        is_twophase_started tphl γ dinit objs_dom j K e1 e1 }}}.
  Proof.
    iIntros (Φ) "(?&Hatom) HΦ".
    iNamed.
    iNamed "Htwophase".
    wp_apply (wp_TwoPhase__Begin_raw with "[$]"); first by assumption.
    iIntros (?) "?".
    iNamed.
    iApply "HΦ".
    iExists (∅, ∅), (∅, ∅), _, _.
    iFrame.
    iPureIntro.
    split.
    - apply always_steps_refl.
      rewrite /wf_jrnl /offsets_aligned /sizes_correct dom_empty_L /=.
      set_solver.
    - rewrite /jrnl_maps_have_mt_changed /=.
      split; first by reflexivity.
      rewrite map_zip_empty_r.
      apply map_Forall_empty.
  Qed.

  Theorem wp_TwoPhase__CommitNoRelease' l γ dinit objs_dom j K e1 v :
    {{{ is_twophase_started l γ dinit objs_dom j K e1 (SOMEV v) }}}
      TwoPhase__CommitNoRelease #l
    {{{ (ok:bool), RET #ok;
        if ok then
          is_twophase_releasable l γ objs_dom ∗
          j ⤇ K (SOMEV v)
        else
          is_twophase_started l γ dinit objs_dom j K e1 (SOMEV v)
    }}}.
  Proof. Admitted.

  Theorem twophase_started_abort l γ dinit objs_dom j K e1 e2 :
    is_twophase_started l γ dinit objs_dom j K e1 e2 -∗
    |NC={⊤}=> is_twophase_releasable l γ objs_dom ∗
              j ⤇ K NONEV.
  Proof. Admitted.

  Theorem wp_TwoPhase__ReleaseAll' l γ objs_dom :
    {{{ is_twophase_releasable l γ objs_dom }}}
      TwoPhase__ReleaseAll #l
    {{{ RET #(); True }}}.
  Proof. Admitted.

  Theorem wp_TwoPhase__ReadBuf' l γ dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ext_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K} e1 a sz :
    {{{
      is_twophase_started l γ dinit objs_dom j K0 e1
        (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
          ReadBufOp (PairV (addr2val' a) #sz)))
    }}}
      TwoPhase__ReadBuf' #l (addr2val a, #sz)
    {{{ v, RET (val_of_obj v);
        is_twophase_started l γ dinit objs_dom j K0 e1
          (K (val_of_obj' v))
    }}}.
  Proof. Admitted.

  Theorem wp_TwoPhase__OverWrite' l γ dinit objs_dom j K0 K
          {Hctx: LanguageCtx'
            (ext := @spec_ext_op_field _)
            (ffi := (spec_ffi_model_field))
            (ffi_semantics := (spec_ext_semantics_field))
            K}  e1 a ov :
    {{{
      is_twophase_started l γ dinit objs_dom j K0
        e1
        (K (ExternalOp (ext := @spec_ext_op_field jrnl_spec_ext)
          OverWriteOp (PairV (addr2val' a) (val_of_obj' ov)))) }}}
      TwoPhase__OverWrite' #l (addr2val a, val_of_obj ov)
    {{{ RET #();
        is_twophase_started l γ dinit objs_dom j K0
                            e1 (K #())
    }}}.
  Proof. Admitted.

  Lemma twophase_started_step_puredet l γ dinit objs_dom j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e1 e2:
    (∀ σ, prim_step' e1 σ [] e2 σ []) →
    is_twophase_started l γ dinit objs_dom j K0 e0 (K e1) -∗
    is_twophase_started l γ dinit objs_dom j K0 e0 (K e2).
  Proof. Admitted.

  Lemma twophase_started_ub_det l γ dinit objs_dom E j K0 K
        `{Hctx: LanguageCtx'
          (ext := @spec_ext_op_field _)
          (ffi := (spec_ffi_model_field))
          (ffi_semantics := (spec_ext_semantics_field))
          K} e0 e :
    nclose sN ⊆ E →
    (∀ s, stuck' e s) →
    is_twophase_started l γ dinit objs_dom j K0 e0 (K e)
    -∗ |NC={E}=> False.
  Proof. Admitted.

End proof.
