From Perennial.program_proof.mvcc Require Import
     mvcc_prelude mvcc_ghost mvcc_inv
     db_repr db_mk db_new_txn db_activate_gc
     txn_repr txn_read txn_write txn_delete txn_run strnum.
From Goose.github_com.mit_pdos.vmvcc Require Import examples.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition view_xfer (src dst : u64) (sbal dbal : u64) : dbmap :=
  {[ src := Some (u64_to_string sbal); dst := Some (u64_to_string dbal) ]}.

Definition P (src dst : u64) (r : dbmap) :=
  src ≠ dst ∧
  ∃ (sbal dbal : u64), r = view_xfer src dst sbal dbal.

Definition rel_bals_amt (sbalr dbalr sbalw dbalw amt : u64) :=
  (uint.Z sbalr) - (uint.Z amt) = (uint.Z sbalw) ∧
  (uint.Z dbalw) - (uint.Z amt) = (uint.Z dbalr).

Definition Q (src dst : u64) (amt : u64) (r w : dbmap) :=
  ∃ (sbalr dbalr sbalw dbalw : u64),
    r = view_xfer src dst sbalr dbalr ∧
    w = view_xfer src dst sbalw dbalw ∧
    rel_bals_amt sbalr dbalr sbalw dbalw amt.

Lemma Q_dom_r_w_eq src dst amt r w :
  Q src dst amt r w -> dom r = dom w.
Proof.
  intros HQ.
  destruct HQ as (sbalr & dbalr & sbalw & dbalw & Hr & Hw & _).
  set_solver.
Qed.

Theorem wp_xfer (txn : loc) (tid : nat) (src : u64) (dst : u64) (amt : u64) r γ τ :
  {{{ own_txn txn tid r γ τ ∗ txnmap_ptstos τ r ∗  ⌜P src dst r⌝ }}}
    xfer #txn #src #dst #amt
  {{{ (ok : bool), RET #ok;
      own_txn txn tid r γ τ ∗
      if ok
      then ∃ w, txnmap_ptstos τ w ∗ ⌜Q src dst amt r w⌝
      else True
  }}}.
Proof.
  iIntros (Φ) "(Htxn & Hpts & %HP) HΦ".
  wp_rec. wp_pures.
  unfold txnmap_ptstos.
  destruct HP as (Hneq & sbal & dbal & Hr).
  (* Break [txnmap_ptstos τ r] into two pieces: one for [src] and one for [dst]. *)
  rewrite Hr big_sepM_insert; last by apply lookup_singleton_ne.
  iDestruct "Hpts" as "[Hsrc Hdst]".
  rewrite big_sepM_singleton.

  (*@ func xfer(txn *vmvcc.Txn, src, dst, amt uint64) bool {                  @*)
  (*@     sbalx, _ := txn.Read(src)                                           @*)
  (*@                                                                         @*)
  wp_apply (wp_txn__Read_found with "[$Htxn $Hsrc]").
  iIntros "[Htxn Hsrc]".
  wp_pures.

  (*@     sbal := strnum.StringToU64(sbalx)                                   @*)
  (*@                                                                         @*)
  wp_apply (wp_StringToU64).
  { iPureIntro. reflexivity. }
  iIntros (sbal' Hsbal').
  apply u64_to_string_inj in Hsbal'. subst sbal'.
  wp_pures.
  
  (*@     if sbal < amt {                                                     @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }
  rewrite Z.nlt_ge in Heqb.
  rename Heqb into Hamt_sbal.
  wp_pures.
  
  (*@     sbaly := strnum.U64ToString(sbal - amt)                             @*)
  (*@                                                                         @*)
  wp_apply (wp_U64ToString).
  iIntros (sbaly Hsbaly).
  wp_pures.

  (*@     txn.Write(src, sbaly)                                               @*)
  (*@                                                                         @*)
  wp_apply (wp_txn__Write with "[$Htxn $Hsrc]").
  iIntros "[Htxn Hsrc]".
  wp_pures.
  
  (*@     dbalx, _ := txn.Read(dst)                                           @*)
  (*@     dbal := strnum.StringToU64(dbalx)                                   @*)
  (*@                                                                         @*)
  wp_apply (wp_txn__Read_found with "[$Htxn $Hdst]").
  iIntros "[Htxn Hdst]".
  wp_pures.
  wp_apply (wp_StringToU64).
  { iPureIntro. reflexivity. }
  iIntros (dbal' Hdbal').
  apply u64_to_string_inj in Hdbal'. subst dbal'.
  wp_pures.

  (*@     if dbal + amt < dbal {                                              @*)
  (*@         return false                                                    @*)
  (*@     }                                                                   @*)
  (*@                                                                         @*)
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }
  rewrite Z.nlt_ge in Heqb.
  rename Heqb into Hamt_dbal.
  wp_pures.

  (*@     dbaly := strnum.U64ToString(dbal + amt)                             @*)
  (*@     txn.Write(dst, dbaly)                                               @*)
  (*@                                                                         @*)
  wp_apply (wp_U64ToString).
  iIntros (dbaly Hdbaly).
  wp_pures.
  wp_apply (wp_txn__Write with "[$Htxn $Hdst]").
  iIntros "[Htxn Hdst]".
  wp_pures.
  
  (*@     return true                                                         @*)
  (*@ }                                                                       @*)
  iApply "HΦ".
  iFrame.
  iExists ({[ src := Some sbaly; dst := Some dbaly ]}).
  iModIntro. iSplit.
  { rewrite big_sepM_insert; last by apply lookup_singleton_ne.
    rewrite big_sepM_singleton.
    by iFrame.
  }
  iPureIntro.
  unfold Q.
  exists sbal, dbal, (word.sub sbal amt), (word.add dbal amt).
  split; first reflexivity.
  unfold view_xfer.
  rewrite Hsbaly Hdbaly.
  split; first reflexivity.
  split; first word.
  clear -Hamt_dbal.
  rewrite ModArith.sum_nooverflow_l; [word | done].
Qed.

Definition dbpts_xfer γ (src dst : u64) (sbal dbal : u64) : iProp Σ :=
  "Hsrc" ∷ dbmap_ptsto γ src 1 (Some (u64_to_string sbal)) ∗
  "Hdst" ∷ dbmap_ptsto γ dst 1 (Some (u64_to_string dbal)).

Lemma dbpts_xfer_neq γ (src dst : u64) (sbal dbal : u64) :
  dbpts_xfer γ src dst sbal dbal -∗
  ⌜src ≠ dst⌝.
Proof.
  iIntros "Hpts".
  iNamed "Hpts".
  by iDestruct (ghost_map.ghost_map_elem_ne with "Hsrc Hdst") as "%Hneq".
Qed.

Lemma view_dbpts_xfer γ src dst sbal dbal :
  src ≠ dst ->
  dbmap_ptstos γ 1 (view_xfer src dst sbal dbal) -∗
  dbpts_xfer γ src dst sbal dbal.
Proof.
  iIntros (Hneq) "Hdbpts".
  unfold dbmap_ptstos.
  rewrite big_sepM_insert; last by apply lookup_singleton_ne.
  iDestruct "Hdbpts" as "[Hsrc Hdst]".
  rewrite big_sepM_singleton.
  by iFrame.
Qed.

Theorem wp_AtomicXfer (txno : loc) (src dst : u64) (amt : u64) γ :
  ⊢ {{{ own_txn_uninit txno γ }}}
    <<< ∀∀ (sbalr dbalr : u64), dbpts_xfer γ src dst sbalr dbalr >>>
      AtomicXfer #txno #src #dst #amt @ ↑mvccN
    <<< ∃∃ (ok : bool) (sbalw dbalw : u64),
          if ok
          then dbpts_xfer γ src dst sbalw dbalw ∗
               ⌜rel_bals_amt sbalr dbalr sbalw dbalw amt⌝
          else dbpts_xfer γ src dst sbalr dbalr
   >>>
   {{{ RET #ok; own_txn_uninit txno γ }}}.
Proof.
  iIntros "!>".
  iIntros (Φ) "Htxn HAU".
  wp_rec. wp_pures.

  (*@ func AtomicXfer(txno *vmvcc.Txn, src, dst, amt uint64) bool {           @*)
  (*@     body := func(txni *vmvcc.Txn) bool {                                @*)
  (*@         return xfer(txni, src, dst, amt)                                @*)
  (*@     }                                                                   @*)
  (*@     return txno.Run(body)                                               @*)
  (*@ }                                                                       @*)
  (* Q: Does fupd commute with exists? *)
  wp_apply (wp_txn__Run_xres _ _ (P src dst) (Q src dst amt) with "[$Htxn]").
  { unfold spec_body_xres.
    clear Φ.
    iIntros (tid r τ Φ) "(Htxn & %HP & Htxnpts) HΦ".
    wp_pures.
    wp_apply (wp_xfer with "[$Htxn $Htxnpts]"); first done.
    iIntros (ok) "[Htxn Hpost]".
    iApply "HΦ".
    iFrame.
    destruct ok; last done.
    iDestruct "Hpost" as (w) "[Hpost %HQ]".
    iExists w.
    iFrame.
    iPureIntro.
    split; first done.
    by eapply Q_dom_r_w_eq.
  }
  iMod "HAU".
  iModIntro.
  iDestruct "HAU" as (sbalr dbalr) "[Hdbpts HAU]".
  iDestruct (dbpts_xfer_neq with "Hdbpts") as "%Hneq".
  iExists (view_xfer src dst sbalr dbalr).
  iSplitL "Hdbpts".
  { iSplit.
    { unfold view_xfer, P.
      iPureIntro.
      split; [done | eauto].
    }
    iNamed "Hdbpts".
    unfold dbmap_ptstos.
    unfold view_xfer.
    rewrite big_sepM_insert; last by apply lookup_singleton_ne.
    rewrite big_sepM_singleton.
    iFrame.
  }
  iIntros (ok w).
  destruct ok.
  { (* Case COMMIT. *)
    iIntros "[%HQ Hdbpts]".
    destruct HQ as (sbalr' & dbalr' & sbalw & dbalw & Hr & Hw & Hrel).
    (* Deducing [sbalr' = sbalr] and [dbalr' = dbalr]. *)
    unfold view_xfer in Hr.
    rewrite map_eq_iff in Hr.
    pose proof (Hr src) as Hsrc.
    do 2 rewrite lookup_insert_eq in Hsrc.
    (* Q: What's SSR way of rewriting multiple times? *)
    inversion Hsrc. apply u64_to_string_inj in H0. subst sbalr'.
    pose proof (Hr dst) as Hdst.
    rewrite lookup_insert_ne in Hdst; last done.
    rewrite lookup_insert_eq in Hdst.
    rewrite lookup_insert_ne in Hdst; last done.
    rewrite lookup_insert_eq in Hdst.
    inversion Hdst. apply u64_to_string_inj in H0. subst dbalr'.
    clear Hr Hsrc Hdst.
    (* Should have a nicer proof...? *)
    iDestruct ("HAU" $! true sbalw dbalw with "[Hdbpts]") as "HAU"; last done.
    { iSplit; last done.
      rewrite Hw.
      iApply view_dbpts_xfer; done.
    }
  }
  { (* Case ABORT. *)
    iIntros "Hdbpts".
    iDestruct ("HAU" $! false (W64 0) (W64 0) with "[Hdbpts]") as "HAU"; last done.
    iApply view_dbpts_xfer; done.
  }
Qed.

End program.
