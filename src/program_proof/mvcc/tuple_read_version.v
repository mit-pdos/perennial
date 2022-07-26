From Perennial.program_proof.mvcc Require Import tuple_common.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*******************************************************************)
(* func findRightVer(tid uint64, vers []Version) Version           *)
(*******************************************************************)
Local Theorem wp_findRightVer (tid : u64) (versS : Slice.t)
                              (vers : list (u64 * bool * u64)) :
  {{{ ⌜∃ (ver : pver), (ver ∈ vers) ∧ (int.Z ver.1.1 < int.Z tid)⌝ ∗
      slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers)
  }}}
    findRightVer #tid (to_val versS)
  {{{ (ver : pver), RET (ver_to_val ver);
      ⌜spec_find_ver vers tid = Some ver⌝ ∗
      slice.is_slice versS (structTy Version) 1 (ver_to_val <$> vers)
  }}}.
Proof.
  iIntros (Φ) "[%Hlt HversS] HΦ".
  destruct Hlt as [ver'' [Hin Hlt]].
  destruct (nil_or_length_pos vers) as [| Hnonempty].
  { rewrite H in Hin. by destruct (not_elem_of_nil ver''). }
  iDestruct (slice.is_slice_small_acc with "HversS") as "[HversS HversC]".
  iDestruct (is_slice_small_sz with "HversS") as "%HversLen".
  rewrite fmap_length in HversLen.
  wp_call.
  
  (***********************************************************)
  (* var ver Version                                         *)
  (* length := uint64(len(vers))                             *)
  (* var idx uint64 = 0                                      *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first auto.
  iIntros (verR) "HverR".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_ref_to); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.

  (***********************************************************)
  (* for {                                                   *)
  (*     if idx >= length {                                  *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     ver = vers[length - (1 + idx)]                      *)
  (*     if tid > ver.begin {                                *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx++                                               *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (ver : u64 * bool * u64) (idx : u64),
             "HverR" ∷ (verR ↦[struct.t Version] ver_to_val ver) ∗
             "HidxR" ∷ (idxR ↦[uint64T] #idx) ∗
             "HversS" ∷ is_slice_small versS (struct.t Version) 1 (ver_to_val <$> vers) ∗
             "%Hspec" ∷ if b
                        then ⌜spec_find_ver_reverse (take (int.nat idx) (reverse vers)) tid = None⌝
                        else ⌜spec_find_ver_reverse (reverse vers) tid = Some ver⌝)%I.
  wp_apply (wp_forBreak P with "[] [-HΦ HversC]").
  { (* Loop body. *)
    clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "Hloop HΦ".
    iNamed "Hloop".
    wp_pures.
    wp_load.
    wp_pures.
    wp_if_destruct.
    { (* Exceeding the bound. *)
      iModIntro.
      iApply "HΦ".
      unfold P.
      replace (take (int.nat idx) _) with (reverse vers) in Hspec; last first.
      { symmetry.
        pose proof (reverse_length vers) as HversRevLen.
        rewrite take_ge; first done.
        rewrite HversRevLen HversLen.
        word.
      }
      destruct (spec_find_ver_lt_Some _ _ _ Hin Hlt).
      unfold spec_find_ver in H.
      by rewrite H in Hspec.
    }
    wp_load.
    wp_pures.
    
    apply Znot_le_gt in Heqb.
    destruct (list_lookup_lt _ vers (length vers - S (int.nat idx))%nat) as [ver' Hver']; first word.
    wp_apply (wp_SliceGet with "[HversS]").
    { iFrame.
      iPureIntro.
      set x := versS.(Slice.sz).
      (**
       * Notes on rewriting between [word.sub] and [Z.sub].
       * 1. In general, to rewrite from [int.Z (word.sub x y)] to [int.Z x - int.Z y],
       * we need to have [int.Z x ≥ int.Z y] in the context.
       * 2. For nested [word.sub], e.g., [int.Z (word.sub (word.sub x y) z)], we can
       * first prove that [int.Z (word.sub x y) ≥ int.Z z], and then replace
       * [int.Z (word.sub (word.sub x y) z)] with [int.Z x - int.Z y - int.Z z].
       *)
      assert (H : Z.ge (int.Z (word.sub x idx)) 1).
      { subst x. word. }
      replace (int.Z (word.sub _ (U64 1))) with (int.Z versS.(Slice.sz) - int.Z idx - 1); last first.
      { subst x. word. }
      replace (Z.to_nat _) with ((length vers) - (S (int.nat idx)))%nat; last first.
      { rewrite HversLen. word. }
      rewrite list_lookup_fmap.
      rewrite Hver'.
      by apply fmap_Some_2.
    }
    iIntros "[HversS %Hvalty]".
    wp_store.
    wp_load.
    wp_pures.
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      unfold P.
      do 2 iExists _.
      iFrame "∗ %".
      iPureIntro.
      rewrite -reverse_lookup in Hver'; last first.
      { rewrite HversLen. word. }
      apply take_drop_middle in Hver'.
      apply (spec_find_ver_reverse_match _ _ _ _ _ Hver'); [done | word].
    }
    wp_load.
    wp_store.
    iModIntro.
    iApply "HΦ".
    unfold P.
    do 2 iExists _.
    iFrame.
    iPureIntro.
    replace (int.nat (word.add _ _)) with (S (int.nat idx)); last word.
    rewrite -reverse_lookup in Hver'; last first.
    { rewrite HversLen. word. }
    rewrite (take_S_r _ _ ver'); last done.
    set vers_take := take _ _.
    set vers' := vers_take ++ _.
    apply Znot_lt_ge in Heqb0.
    apply (spec_find_ver_reverse_not_match vers' _ vers_take ver'); [auto | auto | word].
  }
  { (* Loop entry. *)
    unfold P.
    iExists (U64 0, false, U64 0).
    iExists _.
    iFrame.
    iPureIntro.
    change (int.nat 0) with 0%nat.
    rewrite take_0.
    split; auto.
  }
  iIntros "Hloop".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return ver                                              *)
  (***********************************************************)
  wp_load.
  iApply "HΦ".
  iDestruct ("HversC" with "HversS") as "HversS".
  by iFrame.
Qed.

(**
 * 1. [view_ptsto] in the postcondition can be obtained by applying
 *    the invariant between the logical and physical version chains to
 *    reading a physical verison.
 * 2. However, when GC is involved, the invariant should hold only for
 *    those physical versions created after a certain tid (the
 *    [tidlbN] in [own_tuple]).
 *    Thus, we need a proof of [(int.nat tid) ≥ tidlbN] in order to
 *    apply the invariant, which can be proved by:
 *    - [active_tid γ sid tid] in the precondition.
 *    - [min_tid_lb γ tidlbN] in the lock invariant.
 *)

Definition tuple_read tuple tid key val found γ : iProp Σ :=
  ∃ (tidown tidlast tidgc : u64) (vers : list pver)
    (vchain : list dbval),
    (* physical state is updated, but logical state is not. *)
    let tidlast' := if bool_decide (int.Z tidlast < int.Z tid)
                    then tid
                    else tidlast
    in
    "Hphys" ∷ own_tuple_phys tuple tidown tidlast' vers ∗
    "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
    "%Htid" ∷ ⌜int.Z tid ≤ int.Z tidlast ∨ int.Z tidown = 0⌝ ∗
    "%Hret" ∷ ⌜spec_lookup vers tid = to_dbval found val⌝.

Definition per_key_cmt_inv_def key tmods m past future γ : iProp Σ :=
  per_key_inv_def γ key tmods m past ∗ cmt_inv_def γ tmods future.

Lemma tuple_read_safe tid key tmods m past future tuple val found γ :
  head_read future tid key ->
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods m past) -∗
  cmt_inv_def γ tmods future -∗
  tuple_read tuple tid key val found γ ==∗
  ([∗ set] k ∈ keys_all, per_key_inv_def γ k tmods m (past ++ [EvRead tid key])) ∗
  cmt_inv_def γ tmods future ∗
  own_tuple tuple key γ ∗
  view_ptsto γ key (to_dbval found val) tid.
Admitted.

(*
Lemma case_tuple__ReadVersion tuple tid key val (ret : u64) γ :
  post_tuple__ReadVersion tuple tid key val ret γ -∗
  ⌜int.Z ret = 0 ∨ int.Z ret = 1⌝.
Proof.
  iIntros "H".
  iNamed "H".
Admitted.
 *)

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, uint64)  *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple (tid : u64) (key : u64) (sid : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid sid }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : u64) (found : bool) (latch : loc), RET (#val, #found);
      active_tid γ tid sid ∗
      tuple_locked tuple key latch γ ∗
      tuple_read tuple tid key val found γ
  }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> Hactive HΦ".
  iNamed "Htuple".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  wp_pures.

  (***********************************************************)
  (* for tid > tuple.tidlast && tuple.tidown != 0 {          *)
  (*     tuple.rcond.Wait()                                  *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool),
             (∃ (tidown tidlast tidgc : u64) (vers : list pver) (vchain : list dbval),
                 "Hphys" ∷ own_tuple_phys tuple tidown tidlast vers ∗
                 "Habst" ∷ own_tuple_abst key tidown tidlast tidgc vers vchain γ ∗
                 "Hlocked" ∷ locked #latch ∗
                 "%Hexit" ∷ if b then ⌜True⌝ else ⌜(int.Z tid) ≤ (int.Z tidlast) ∨ (int.Z tidown) = 0⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [-HΦ Hactive]").
  { (* Loop body preserves the invariant. *)
    clear Φ.
    clear tidown tidlast tidgc vers vchain.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    iNamed "Hphys".
    wp_pures.
    wp_loadField.
    wp_pures.
    (**
     * Directly applying [wp_and] seems to bind the wrong [if].
     * Reason: Goose generate a similar form for loops with conds and
     * logical ands.
     * Solution here is using [wp_bind] to focus on the right [if]:
     * [wp_bind (If #(bool_decide _) _ _)].
     *)
    wp_bind (If #(bool_decide _) _ _).
    wp_apply (wp_and with "Htidown").
    { (* Case: [tid > tidlast]. *)
      wp_pures. done.
    }
    { (* Case: [tuple.tidown ≠ 0]. *)
      iIntros "_ Htidown".
      wp_loadField.
      wp_pures.
      rewrite -bool_decide_not.
      eauto with iFrame.
    }
    iIntros "Htidown".
    wp_if_destruct.
    { (* Loop body. *)
      wp_pures.
      wp_loadField.
      wp_apply (wp_condWait with "[-HΦ]").
      { eauto 15 with iFrame. }
      iIntros "[Hlocked HtupleOwn]".
      iNamed "HtupleOwn".
      wp_pures.
      iModIntro.
      iApply "HΦ".
      unfold P.
      eauto 15 with iFrame.
    }
    (* Exiting loop. *)
    iApply "HΦ".
    apply not_and_l in Heqb.
    destruct Heqb; (iModIntro; do 5 iExists _; iFrame "Hlocked Habst").
    { (* Case [verLast.begin ≥ tid]. *)
      iSplitR ""; first eauto 10 with iFrame.
      iPureIntro.
      left. word.
    }
    { (* Case [tuple.tidown = 0]. *)
      iSplitR ""; first eauto 10 with iFrame.
      iPureIntro.
      right.
      apply dec_stable in H.
      by inversion H.
    }
  }
  { (* The invariant holds at the start. *)
    unfold P.
    eauto 10 with iFrame.
  }
  clear tidown tidlast tidgc vers vchain.
  iIntros "Hloop".
  iNamed "Hloop".
  iNamed "Hphys".
  iNamed "Habst".
  iNamed "Hwellformed".
  wp_pures.

  (***********************************************************)
  (* ver := findRightVer(tid, tuple.vers)                    *)
  (***********************************************************)
  wp_loadField.
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iAssert (⌜int.Z tid > 0⌝)%I with "[Hactive]" as "%HtidGZ".
  { iDestruct "Hactive" as "[_ %H]". iPureIntro. word. }
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  wp_apply (wp_findRightVer with "[$HversS]").
  { iPureIntro.
    setoid_rewrite Exists_exists in HexistsLt.
    apply HexistsLt; [word | done].
  }
  iIntros (ver) "[%Hspec HversS]".
  wp_pures.

  (***********************************************************)
  (* if tuple.tidlast < tid {                                *)
  (*     tuple.tidlast = tid                                 *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_If_join_evar with "[Htidlast]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { (* Case [tuple.tidlast < tid]. *)
      wp_if_true.
      wp_storeField.
      iSplit; first done.
      (* Update "Htidrd" to use `b'` for merging states. See comments of wp_If_join_evar in control.v. *)
      replace #tid with #(if b' then tid else tidlast) by by rewrite Eb'.
      iNamedAccu.
    }
    { (* Case [tuple.tidlast ≥ tid]. *)
      wp_if_false.
      iModIntro.
      rewrite Eb'.
      by iFrame.
    }
  }
  iIntros "H".
  iNamed "H".
  wp_pures.

  (***********************************************************)
  (* return ver.val, !ver.deleted                            *)
  (***********************************************************)
  (* Set Printing Coercions. *)
  repeat rewrite ite_apply.
  iModIntro.
  iApply "HΦ".
  iFrame "Hactive".
  iSplitL "Hlocked".
  { iFrame "# ∗". }
  unfold tuple_read.
  do 5 iExists _.
  iSplitL "Htidown Hvers HversS Htidlast".
  { eauto with iFrame. }
  iSplitL "Hvchain".
  { iFrame "% # ∗". }
  iFrame "%".
  iPureIntro.
  unfold spec_lookup.
  rewrite Hspec.
  destruct (negb ver.1.2) eqn:E.
  - rewrite negb_true_iff in E. by rewrite E.
  - rewrite negb_false_iff in E. by rewrite E.
Qed.

End proof.
