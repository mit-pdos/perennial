(* Import definitions/theorems of the Perennial framework with the disk FFI. *)
From Perennial.program_proof Require Export disk_prelude.
(* Import Coq model of our Goose program.*)
From Goose.github_com.mit_pdos.go_mvcc Require Import tuple.
From Perennial.program_proof.mvcc Require Import mvcc_ghost.

Section heap.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition TID_SENTINEL := (U64 18446744073709551615).
Definition RET_SUCCESS := (U64 0).
Definition RET_NONEXIST := (U64 1).
Definition RET_RETRY := (U64 100).
Definition RET_UNSERIALIZABLE := (U64 200).

Definition ver_to_val (x : u64 * u64 * u64) :=
  (#x.1.1, (#x.1.2, (#x.2, #())))%V.

Definition match_ver (tid : u64) (ver : u64 * u64 * u64) :=
  int.Z ver.1.1 < int.Z tid ≤ int.Z ver.1.2.

Definition no_match_vers tid versL :=
  Forall (λ ver, ¬(match_ver tid ver)) versL.

Definition pver_abs_present tid (vchain : list (option u64)) ver :=
  match_ver tid ver -> vchain !! (int.nat tid) = Some (Some ver.2).

Definition pvers_abs_present tid vchain pvers verlast :=
  (Forall (λ ver, pver_abs_present tid vchain ver)) pvers ∧ (pver_abs_present tid vchain verlast).

Definition pvers_abs_absent tid (vchain : list (option u64)) (tidlast : u64) pvers verlast :=
  int.Z tid ≤ int.Z tidlast ->
  no_match_vers tid pvers  ->
  no_match_vers tid [verlast] ->
  vchain !! (int.nat tid) = Some None.

Definition tuple_abs (tid : u64) (vchain : list (option u64)) (tidlast : u64) (verlast : u64 * u64 * u64) (versL : list (u64 * u64 * u64)) :=
  let verlast' := if decide (verlast.1.2 = TID_SENTINEL)
                  then (verlast.1.1, tidlast, verlast.2)
                  else verlast in
  pvers_abs_present tid vchain versL verlast' ∧
  pvers_abs_absent tid vchain tidlast versL verlast'.

Definition tuple_wellformed (tidlast : u64) (verlast : u64 * u64 * u64) :=
  int.Z verlast.1.1 ≤ int.Z tidlast.

Definition own_tuple (tuple : loc) (key : u64) (tidown tidlast : u64) verlast versL (γ : mvcc_names) : iProp Σ :=
  ∃ (vers : Slice.t) (tidlbN : nat) (vchain : list (option u64)),
    "Htidown" ∷ tuple ↦[Tuple :: "tidown"] #tidown ∗
    "Htidlast" ∷ tuple ↦[Tuple :: "tidlast"] #tidlast ∗
    "Hverlast" ∷ tuple ↦[Tuple :: "verlast"] (ver_to_val verlast) ∗
    "Hvers" ∷ tuple ↦[Tuple :: "vers"] (to_val vers) ∗
    "HversL" ∷ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) ∗
    "HtidlbN" ∷  min_tid_lb γ tidlbN ∗
    "%Hwellformed" ∷ ⌜tuple_wellformed tidlast verlast⌝ ∗
    "%HtupleAbs" ∷ (∀ tid, ⌜tuple_abs tid vchain tidlast verlast versL⌝) ∗
    "Hvchain" ∷ (if decide (tidown = (U64 0))
                 then vchain_ptsto γ (1/2) key vchain
                 else vchain_ptsto γ (1/4) key vchain) ∗
    (*
    "HtupleAbs" ∷ ∀ tid, ⌜tidlbN ≤ int.nat tid -> (tuple_abs vchain tidlast verlast versL tid)⌝ ∗
     *)
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (own_tuple _ _ _ _ _ _ _)) => unfold own_tuple : core.

Definition is_tuple (tuple : loc) (key : u64) (γ : mvcc_names) : iProp Σ :=
  ∃ (latch : loc) (rcond : loc),
    "#Hlatch" ∷ readonly (tuple ↦[Tuple :: "latch"] #latch) ∗
    "#Hlock" ∷ is_lock mvccN #latch (∃ tidown tidlast verlast versL, own_tuple tuple key tidown tidlast verlast versL γ) ∗
    "#Hrcond" ∷ readonly (tuple ↦[Tuple :: "rcond"] #rcond) ∗
    "#HrcondC" ∷ is_cond rcond #latch ∗
    "_" ∷ True.
Local Hint Extern 1 (environments.envs_entails _ (is_tuple _ _ _)) => unfold is_tuple : core.

Lemma val_to_ver_with_lookup (x : val) (l : list (u64 * u64 * u64)) (i : nat) :
  (ver_to_val <$> l) !! i = Some x ->
  (∃ (b e v : u64), x = ver_to_val (b, e, v) ∧ l !! i = Some (b, e, v)).
Proof.
  intros H.
  apply list_lookup_fmap_inv in H as [[[y1 y2] y3] [Heq Hsome]].
  naive_solver.
Qed.

(*******************************************************************)
(* func findRightVer(tid uint64, vers []Version) (Version, uint64) *)
(*******************************************************************)
Local Theorem wp_findRightVer (tid : u64) (vers : Slice.t)
                              (versL : list (u64 * u64 * u64)) :
  {{{ slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL) }}}
    findRightVer #tid (to_val vers)
  {{{ (ver : (u64 * u64 * u64)) (ret : u64), RET (ver_to_val ver, #ret);
      ⌜(ret = RET_NONEXIST ∧ no_match_vers tid versL) ∨
       (ret = RET_SUCCESS ∧ match_ver tid ver ∧ ver ∈ versL)⌝ ∗
      slice.is_slice vers (structTy Version) 1 (ver_to_val <$> versL)
  }}}.
Proof.
  iIntros (Φ) "HversL HΦ".
  iDestruct (slice.is_slice_small_acc with "HversL") as "[HversL HversL_close]".
  iDestruct (is_slice_small_sz with "HversL") as "%HversLen".
  rewrite fmap_length in HversLen.
  wp_call.
  
  (***********************************************************)
  (* var ver Version                                         *)
  (* var ret uint64 = common.RET_NONEXIST                    *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first auto.
  iIntros (verR) "HverR".
  wp_pures.
  wp_apply wp_ref_to; first auto.
  iIntros (retR) "HretR".

  (***********************************************************)
  (* for _, v := range vers {                                *)
  (*     if v.begin < tid && tid <= v.end {                  *)
  (*         ver = v                                         *)
  (*         ret = common.RET_SUCCESS                        *)
  (*     }                                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P:= (λ (i : u64), ∃ (ver : u64 * u64 * u64) (ret : u64),
             "HverR" ∷ (verR ↦[struct.t Version] ver_to_val ver) ∗
             "HretR" ∷ (retR ↦[uint64T] #ret) ∗
             "%Hright" ∷ (⌜(ret = RET_NONEXIST ∧ (no_match_vers tid (take (int.nat i) versL))) ∨
                           (ret = RET_SUCCESS ∧ (match_ver tid ver) ∧ ver ∈ versL)⌝))%I.
  wp_apply (slice.wp_forSlice P _ _ _ _ _ (ver_to_val <$> versL)
              with "[] [HverR HretR HversL]").
  { (* Loop body preserves the invariant. *)
    clear Φ.
    iIntros (i x Φ).
    iModIntro.
    iIntros "H HΦ".
    iDestruct "H" as "(H & %Hbound & %Hsome)".
    iNamed "H".
    apply val_to_ver_with_lookup in Hsome as (b & e & v & Hx & Hsome).
    subst.
    wp_pures.
    wp_apply (wp_and_pure (int.Z b < int.Z tid)%Z (int.Z tid ≤ int.Z e)%Z with "[] []").
    { wp_pures. done. }
    { iIntros "_".
      wp_pures.
      done.
    }
    wp_if_destruct.
    - (* Is the correct version *)
      wp_store.
      wp_pures.
      wp_store.
      iApply "HΦ".
      iModIntro.
      iExists _, RET_SUCCESS.
      iFrame.
      iPureIntro.
      right.
      by apply elem_of_list_lookup_2 in Hsome.
    - (* Not the correct version *)
      iApply "HΦ".
      iModIntro.
      iExists ver, ret.
      iFrame.
      iPureIntro.
      destruct Hright as [[Hret Hmatch] | [Hret Hmatch]].
      + (* Case [ret = RET_NONEXIST]. *)
        left.
        split; first done.
        unfold no_match_vers.
        replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
        rewrite (take_S_r _ _ (b, e, v)); last auto.
        apply Forall_app_2; first auto.
        by rewrite Forall_singleton.
      + (* Case [ret = RET_SUCCESS]. *)
        right.
        split; auto.
  }
  { (* Loop invariant holds at the begining *)
    iFrame.
    simpl.
    iExists (_, _, _), RET_NONEXIST.
    iFrame.
    iPureIntro.
    left.
    split; first done.
    unfold no_match_vers.
    replace (int.nat 0) with 0%nat by word.
    by rewrite take_0.
  }
  
  (***********************************************************)
  (* return ver, ret                                         *)
  (***********************************************************)
  iIntros "[H HversL]".
  iNamed "H".
  iDestruct ("HversL_close" with "HversL") as "HversL".
  wp_pures.
  wp_load.
  wp_load.
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame.
  iPureIntro.
  rewrite -HversLen in Hright.
  by rewrite firstn_all in Hright.
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
 *    - [active_tid γ tid] in the precondition.
 *    - [min_tid_lb γ tidlbN] in the lock invariant.
 *)
Definition post_tuple__ReadVersion tid key val (ret : u64) γ : iProp Σ :=
  active_tid γ tid ∗
  match int.Z ret with
  | 0 => view_ptsto γ key (Some val) tid
  | 1 => view_ptsto γ key None tid
  | _ => False
  end.

(* Q: Existing tactic does this? *)
Local Lemma ite_apply (A B : Type) (b : bool) (f : A -> B) x y :
  (if b then f x else f y) = f (if b then x else y).
Proof.
  destruct b; done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (uint64, uint64)  *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ active_tid γ tid }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : u64) (ret : u64), RET (#val, #ret); post_tuple__ReadVersion tid key val ret γ }}}.
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
  (* var verLast Version                                     *)
  (* verLast = tuple.verlast                                 *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (verLastRef) "HverLastRef".
  wp_pures.
  wp_loadField.
  wp_store.
  change (uint64T * _)%ht with (struct.t Version).
  wp_pures.

  (***********************************************************)
  (* for tid > verLast.begin && tuple.tidown != 0 {          *)
  (*     tuple.rcond.Wait()                                  *)
  (*     verLast = tuple.verlast                             *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (tidown tidlast : u64) (verlast : u64 * u64 * u64) (versL : list (u64 * u64 * u64)),
             "HtupleOwn" ∷ own_tuple tuple key tidown tidlast verlast versL γ ∗
             "Hlocked" ∷ locked #latch ∗
             "HverLastRef" ∷ verLastRef ↦[struct.t Version] ver_to_val verlast ∗
             "%Hexit" ∷ if b then ⌜True⌝ else ⌜(int.Z tid) ≤ (int.Z verlast.1.1) ∨ (int.Z tidown) = 0⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [-HΦ Hactive]").
  { (* Loop body preserves the invariant. *)
    clear Φ Hwellformed HtupleAbs.
    clear tidown tidlast verlast versL.
    iIntros (Φ) "!> Hloop HΦ".
    unfold P.
    iNamed "Hloop".
    iNamed "HtupleOwn".
    wp_pures.
    wp_load.
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
    { (* Case [verLast.begin ≥ tid]. *)
      wp_pures. done.
    }
    { (* Case [tuple.tidown = 0]. *)
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
      wp_apply (wp_condWait with "[-HΦ HverLastRef]").
      { eauto 15 with iFrame. }
      iIntros "[Hlocked HtupleOwn]".
      iNamed "HtupleOwn".
      wp_pures.
      wp_loadField.
      wp_store.
      iModIntro.
      iApply "HΦ".
      eauto 15 with iFrame.
    }
    (* Exiting loop. *)
    iApply "HΦ".
    apply not_and_l in Heqb.
    destruct Heqb; (iModIntro; do 4 iExists _; iFrame "Hlocked HverLastRef").
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
  clear Hwellformed HtupleAbs.
  clear tidown tidlast verlast versL vchain.
  iIntros "Hloop".
  iNamed "Hloop".
  iNamed "HtupleOwn".
  wp_pures.

  (***********************************************************)
  (* if tid <= verLast.begin {                               *)
  (*     ver, found := findRightVer(tid, tuple.vers)         *)
  (*     tuple.latch.Unlock()                                *)
  (*     return ver.val, found                               *)
  (* }                                                       *)
  (***********************************************************)
  wp_load.
  wp_pures.
  wp_if_destruct.
  { wp_loadField.
    wp_apply (wp_findRightVer with "HversL").
    iIntros (ver ret) "[%Hret HversL]".
    wp_pures.
    wp_loadField.
    (* Before releasing the lock, obtain [vchain_lb]. *)
    iAssert (vchain_lb γ key vchain) with "[Hvchain]" as "#Hvchain_lb".
    { case_decide; by iApply (vchain_witness). }
    wp_apply (release_spec with "[-HΦ Hactive]").
    { eauto 15 with iFrame. }
    wp_pures.
    iApply "HΦ".
    iModIntro.
    unfold post_tuple__ReadVersion.
    iFrame.
    destruct Hret as [[Hret Htid] | (Hret & Htid & Hin)].
    { (* Case: old verions and [ret = RET_NONEXIST]. *)
      rewrite Hret.
      change (int.Z RET_NONEXIST) with 1.
      simpl.
      (* Prove [view_ptsto]. *)
      unfold view_ptsto.
      destruct (HtupleAbs tid) as [_ Habsent].
      unfold pvers_abs_absent in Habsent.
      assert (HNone : vchain !! int.nat tid = Some None).
      { apply Habsent.
        { (* The logical tuple contains something at index [tid]. *)
          unfold tuple_wellformed in Hwellformed.
          apply Z.le_trans with (int.Z verlast.1.1); auto.
        }
        { (* Does not match the old versions. Follows from [wp_findRightVer]. *)
          auto.
        }
        { (* Does not match the last version. *)
          unfold no_match_vers.
          rewrite Forall_singleton.
          unfold match_ver.
          rewrite not_and_l.
          left.
          rewrite Z.nlt_ge.
          case_decide; auto.
        }
      }
      eauto with iFrame.
    }
    { (* Case: old versions and [ret = RET_SUCCESS]. *)
      rewrite Hret.
      change (int.Z RET_SUCCESS) with 0.
      simpl.
      (* Prove [view_ptsto]. *)
      unfold view_ptsto.
      destruct (HtupleAbs tid) as [[Hpresent _] _].
      (* Q: Why do [rewrite] and [apply] fail? *)
      setoid_rewrite Forall_forall in Hpresent.
      apply Hpresent in Hin.
      apply Hin in Htid.
      eauto with iFrame.
    }
  }

  (* Here we can have [tidown = 0] and [tid > verLast.begin]. *)
  destruct Hexit; first contradiction.
  apply Znot_le_gt in Heqb.
    
  (***********************************************************)
  (* var val uint64                                          *)
  (* var ret uint64                                          *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (valRef) "HvalRef".
  wp_apply (wp_ref_of_zero); first done.
  iIntros (retRef) "HretRef".
  wp_pures.
  wp_load.
  wp_pures.

  (***********************************************************)
  (* if tid <= verLast.end {                                 *)
  (*     val = verLast.val                                   *)
  (*     ret = common.RET_SUCCESS                            *)
  (* } else {                                                *)
  (*     ret = common.RET_NONEXIST                           *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_If_join_evar with "[HverLastRef HvalRef HretRef]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { (* Case [tid ≤ verLast.end]. *)
      wp_if_true.
      wp_load.
      wp_pures.
      wp_store.
      wp_store.
      iModIntro.
      iSplit; first done.
      replace #verlast.2 with #(if b' then verlast.2 else (U64 0)) by by rewrite Eb'.
      replace #0 with #(if b' then (U64 0) else (U64 1)) by by rewrite Eb'.
      iNamedAccu.
    }
    { (* Case [tid > verLast.end]. *)
      wp_if_false.
      wp_store.
      iModIntro.
      rewrite Eb'.
      by iFrame.
    }
  }
  iIntros "H".
  iNamed "H".
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

  (**
   * Case 1: [tid > tuple.tidlast] and [tid > tuple.verlast.end].
   * - Extend the logical tuple with [Some None] to index [tid].
   * - Obtain [vchain !! (int.nat tid) = Some None].
   *
   * Case 2: [tid > tuple.tidlast] and [tid ≤ tuple.verlast.end].
   * - Extend the logical tuple with [Some tuple.verlast.val] to index [tid].
   * - Obtain [vchain !! (int.nat tid) = Some tuple.verlast.val].
   *
   * Case 3: [tid ≤ tuple.tidlast] and [tid > tuple.verlast.end].
   * - Obtain [vchain !! (int.nat tid) = Some None] from [pvers_abs_absent].
   *
   * Case 4: [tid ≤ tuple.tidlast] and [tid ≤ tuple.verlast.end].
   * - Obtain [vchain !! (int.nat tid) = Some tuple.verlast.val] from the 2nd conjunct of [pvers_abs_present].
   *)

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hactive HvalRef HretRef]").
  {
  (*
    iFrame "Hlocked Hlock".
    iNext.
    do 7 iExists _.
    rewrite ite_apply.
    iFrame "Htidlast".
    iMod (vchain_update vchain with "Hvchain") as "Hvchain"; first admit.
    iFrame.
    
    iPureIntro.
    split.
    - case_bool_decide.
      + unfold tuple_wellformed. word.
      + done.
    - case_bool_decide.
      + intros tid'.
        destruct (HtupleAbs tid') as [Hpresent Habsent].
        unfold tuple_abs.
        split.
        * case_decide; last auto.
          unfold pvers_abs_present in *.
          destruct Hpresent as [Hprev Hlast].
          split; first done.
          unfold pver_abs_present.
          intros.
   *)
    admit.
  }
  
  wp_pures.
  do 2 wp_load.
  wp_pures.

  (***********************************************************)
  (* return val, ret                                         *)
  (***********************************************************)
  (* Set Printing Coercions. *)
  repeat rewrite ite_apply.
  iApply "HΦ".
  iModIntro.
  unfold post_tuple__ReadVersion.
  iFrame "Hactive".
  case_bool_decide.
  { (* Case [tuple.tidlast ≥ tid]. *)
    change (int.Z 0) with 0.
    simpl.
    (* TODO: Prove [view_ptsto]. *)
    admit.
  }
  { (* Case [tuple.tidlast < tid]. *)
    change (int.Z 1) with 1.
    simpl.
    (* TODO: Prove [view_ptsto]. *)
    admit.
  }
Admitted.

Definition post_tuple__appendVersion tuple tid val key verlast versL γ : iProp Σ :=
  let tidown' := (U64 0) in
  let tidlast' := tid in
  let verslast' := (tid, TID_SENTINEL, val) in
  let end' := if decide (verlast.1.2 = TID_SENTINEL) then tid else verlast.1.2 in
  let versL' := versL ++ [(verlast.1.1, end', verlast.2)] in
  own_tuple tuple key tidown' tidlast' verslast' versL' γ.

(*****************************************************************)
(* func (tuple *Tuple) appendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__appendVersion tuple (tid : u64) (val : u64) (key : u64) tidown tidlast verlast versL γ :
  {{{ own_tuple tuple key tidown tidlast verlast versL γ }}}
    Tuple__appendVersion #tuple #tid #val
  {{{ RET #(); post_tuple__appendVersion tuple tid val key verlast versL γ }}}.
Proof.
  iIntros (Φ) "HtupleOwn HΦ".
  iNamed "HtupleOwn".
  wp_call.

  (***********************************************************)
  (* var verLast Version                                     *)
  (* verLast = tuple.verlast                                 *)
  (* if verLast.end == config.TID_SENTINEL {                 *)
  (*     verLast.end = tid                                   *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first done.
  iIntros (verLastRef) "HverLastRef".
  wp_pures.
  wp_loadField.
  wp_store.
  wp_load.
  change (uint64T * _)%ht with (struct.t Version).
  rewrite struct_fields_split.
  iNamed "HverLastRef".
  wp_apply (wp_If_join_evar with "[-HΦ]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    - wp_if_true.
      wp_storeField.
      iSplit; first done.
      replace #tid with #(if b' then tid else verlast.1.2); last by by rewrite Eb'.
      (* replace tid with (if b' then tid else verlast.1.2); last by by rewrite Eb'. *)
      (* Q: What's the @ in the goal? *)
      iNamedAccu.
    - wp_if_false.
      rewrite Eb'.
      iFrame.
      by iFrame.
  }
  iIntros "H".
  iNamed "H".
  wp_pures.
  set b := bool_decide _.
  set verlast' := (verlast.1.1, (if b then tid else verlast.1.2), verlast.2).
  (* Group struct-field points-to to struct points-to. *)
  iAssert (verLastRef ↦[struct.t Version] (ver_to_val verlast'))%I with "[begin end val]" as "HverLastRef".
  { rewrite struct_fields_split. iFrame. destruct b; eauto. }
  
  (***********************************************************)
  (* tuple.vers = append(tuple.vers, verLast)                *)
  (***********************************************************)
  wp_load.
  wp_loadField.
  wp_apply (wp_SliceAppend' with "[HversL]"); [done | auto | auto |].
  iIntros (vers') "HversL".
  wp_storeField.

  (***********************************************************)
  (* verNext := Version{                                     *)
  (*     begin   : tid,                                      *)
  (*     end     : config.TID_SENTINEL,                      *)
  (*     val     : val,                                      *)
  (* }                                                       *)
  (* tuple.verlast = verNext                                 *)
  (***********************************************************)
  wp_pures.
  wp_storeField.

  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidlast = tid                                     *)
  (***********************************************************)
  do 2 wp_storeField.

  iModIntro.
  iApply "HΦ".
  unfold post_tuple__appendVersion.
  do 3 iExists _.
  unfold named.
  iExactEq "HversL".
  rewrite fmap_app.
  do 2 f_equal.
  simpl.
  do 4 f_equal.
  subst b.
  (* Q: Is there an easier way of proving [if a then x else y = if b then x else y] by proving [a = b]? *)
  case_bool_decide.
  - inversion H. by rewrite H1.
  - rewrite decide_bool_decide.
    case_bool_decide.
    + rewrite H0 in H. unfold TID_SENTINEL in H. congruence.
    + done.
Qed.

(*****************************************************************)
(* func (tuple *Tuple) AppendVersion(tid uint64, val uint64)     *)
(*****************************************************************)
Theorem wp_tuple__AppendVersion tuple (tid : u64) (val : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__AppendVersion #tuple #tid #val
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iDestruct "HtupleOwn" as (tidown tidlast verlast versL) "HtupleOwn".
  wp_pures.
  
  (***********************************************************)
  (* tuple.appendVersion(tid, val)                           *)
  (***********************************************************)
  wp_apply (wp_tuple__appendVersion with "[$HtupleOwn]"); first eauto 10 with iFrame.
  iIntros "HtupleOwn".
  wp_pures.
  
  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  wp_pures.
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  unfold post_tuple__appendVersion.
  wp_apply (release_spec with "[-HΦ]"); first eauto 10 with iFrame.
  wp_pures.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Free(tid uint64)                          *)
(*****************************************************************)
Theorem wp_tuple__Free tuple (tid : u64) (key : u64) (versL : list (u64 * u64 * u64)) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__Free #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
  rename versL into versL'.
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
  (* tuple.tidown = 0                                        *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.rcond.Broadcast()                                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_condBroadcast with "[$HrcondC]").
  wp_pures.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 15 with iFrame. }
  wp_pures.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func (tuple *Tuple) Own(tid uint64) bool                      *)
(*****************************************************************)
Theorem wp_tuple__Own tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__Own #tuple #tid
  {{{ (b : bool), RET #b; if b
                        then mods_token γ key tid
                        else True
  }}}.
Proof.
  iIntros "#Htuple !#" (Φ) "_ HΦ".
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
  (* if tid < tuple.tidrd || tid < tuple.tidwr {             *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return false                                          *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_or with "[Htidwr]").
  { iApply "Htidwr". }
  { wp_pures. done. }
  { iIntros "_ Hidwr". wp_loadField. wp_pures. iFrame. done. }
  iIntros "Hidrwr".
  wp_if_destruct.
  { (* Early return: `tid < tuple.tidrd || tid < tuple.tidwr` *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { eauto 15 with iFrame. }
    wp_pures.
    iModIntro. iApply "HΦ". done.
  }

  (***********************************************************)
  (* if tuple.tidown != 0 {                                  *)
  (*   tuple.latch.Unlock()                                  *)
  (*   return false                                          *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_if_destruct.
  { (* Early return: `tuple.tidown != 0` *)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    { eauto 15 with iFrame. }
    wp_pures.
    by iApply "HΦ".
  }

  (***********************************************************)
  (* tuple.tidown = tid                                      *)
  (***********************************************************)
  wp_storeField.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 15 with iFrame. }
  wp_pures.
  iModIntro.

  (***********************************************************)
  (* return true                                             *)
  (***********************************************************)
  iApply "HΦ".
  admit. (* TODO: prove mods_token *)
Admitted.

Lemma val_to_ver_with_val_ty (x : val) :
  val_ty x (uint64T * (uint64T * (uint64T * unitT))%ht) ->
  (∃ (b e v : u64), x = ver_to_val (b, e, v)).
Proof.
  intros H.
  inversion_clear H. 
  { inversion H0. }
  inversion_clear H0.
  inversion_clear H.
  inversion_clear H1.
  { inversion H. }
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H0.
  { inversion H. }
  inversion_clear H.
  inversion_clear H0.
  inversion_clear H1.
  inversion_clear H.
  exists x0, x1, x2.
  reflexivity.
Qed.

(**
 * The `safe_rm_verchain` says that,
 * 1) the new list is a sublist of the old list (so no new versions can be added).
 * 2) all the versions whose end timestamp is greater than `tid` are preserved.
 *
 * We could additionally specify the performance-related condition as follows:
 * 3) all the versions whose end timestamp is less than or equal to `tid` are removed.
 *)
Definition safe_rm_verchain (tid : u64) (versL versL' : list (u64 * u64 * u64)) :=
  (sublist versL' versL) ∧
  (Forall (fun ver => int.Z ver.1.2 > (int.Z tid) -> ver ∈ versL')) versL.
  
(*****************************************************************)
(* func (tuple *Tuple) removeVersions(tid uint64)                *)
(*****************************************************************)
Theorem wp_tuple__removeVersions tuple (tid : u64) (key : u64) versL γ :
  {{{ own_tuple tuple key versL γ }}}
    Tuple__removeVersions #tuple #tid
  {{{ RET #(); ∃ versL', (own_tuple tuple key versL' γ) ∗ ⌜(safe_rm_verchain tid versL versL')⌝ }}}.
Proof.
  iIntros (Φ) "HtupleOwn HΦ".
  iNamed "HtupleOwn".
  wp_call.

  (***********************************************************)
  (* var idx uint64 = 0                                      *)
  (* for {                                                   *)
  (*   if idx >= uint64(len(tuple.vers)) {                   *)
  (*     break                                               *)
  (*   }                                                     *)
  (*   ver := tuple.vers[idx]                                *)
  (*   if ver.end > tid {                                    *)
  (*     break                                               *)
  (*   }                                                     *)
  (*   idx++                                                 *)
  (* }                                                       *)
  (***********************************************************)
  wp_apply (wp_ref_to); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.
  wp_apply (wp_forBreak
              (λ _,
                (tuple ↦[Tuple :: "vers"] to_val vers) ∗
                (slice.is_slice vers (struct.t Version) 1 (ver_to_val <$> versL)) ∗
                (∃ (idx : u64), (idxR ↦[uint64T] #idx) ∗
                                (⌜int.Z idx ≤ int.Z vers.(Slice.sz)⌝) ∗
                                ([∗ list] k ↦ ver ∈ (take (int.nat idx) versL), ⌜(int.Z ver.1.2) ≤ (int.Z tid)⌝))
                )%I
             with "[] [$Hvers $HversL HidxR]").
  { clear Φ.
    iIntros (Φ).
    iModIntro.
    iIntros "Hinv HΦ".
    iDestruct "Hinv" as "(Hvers & HversL & Hidx)".
    iDestruct "Hidx" as (idx) "(HidxR & %Hbound & HidxOrder)".
    wp_pures.
    wp_loadField.
    wp_apply (wp_slice_len).
    wp_load.
    wp_pures.
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      eauto 10 with iFrame.
    }
    wp_load.
    wp_loadField.
    iDestruct (slice.is_slice_small_acc with "HversL") as "[HversS HversL]".
    iDestruct (slice.is_slice_small_sz with "[$HversS]") as "%HversSz".
    destruct (list_lookup_lt _ (ver_to_val <$> versL) (int.nat idx)) as [ver HSome].
    { apply Z.nle_gt in Heqb.
      word.
    }
    wp_apply (slice.wp_SliceGet with "[HversS]"); first auto.
    iIntros "[HversS %HverT]".
    destruct (val_to_ver_with_val_ty _ HverT) as (b & e & v & H).
    subst.
    wp_pures.
    iDestruct ("HversL" with "HversS") as "HversL".
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      eauto with iFrame.
    }
    wp_load.
    wp_pures.
    wp_store.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iExists (word.add idx 1%Z).
    iFrame.
    iSplit.
    { iPureIntro.
      word.
    }
    { replace (int.nat (word.add idx _)) with (S (int.nat idx)); last word.
      apply list_lookup_fmap_inv in HSome as (y & Heq & HSome).
      rewrite (take_S_r _ _ y); last apply HSome.
      iApply (big_sepL_app).
      iSplit; first done.
      iApply (big_sepL_singleton).
      iPureIntro.
      apply Znot_lt_ge in Heqb0.
      inversion Heq.
      rewrite H1 in Heqb0.
      (* Q: Why can't lia solve this... *)
      rewrite -Z.ge_le_iff.
      apply Heqb0.
    }
  }
  { iExists (U64 0).
    iFrame.
    iSplit.
    - iPureIntro. word.
    - change (int.nat 0) with 0%nat.
      rewrite take_0.
      naive_solver.
  }
  iIntros "(Hvers & HversL & Hidx)".
  iDestruct "Hidx" as (idx) "(HidxR & %Hbound & %HidxOrder)".
  wp_pures.

  (***********************************************************)
  (* tuple.vers = tuple.vers[idx:]                           *)
  (***********************************************************)
  wp_load.
  wp_loadField.
  wp_apply (wp_SliceSkip').
  { eauto. }
  wp_storeField.
  (* Weaken is_slice. Should this go to the slice lib? *)
  iDestruct "HversL" as "[HversS HversC]".
  iDestruct (slice.is_slice_small_take_drop _ _ _ idx with "HversS") as "[HversS _]".
  { word. }
  iDestruct (slice.is_slice_cap_skip _ _ idx with "HversC") as "HversC".
  { word. }
  iDestruct (slice.is_slice_split with "[$HversS $HversC]") as "HversL".
  rewrite <- fmap_drop.

  iApply "HΦ".
  iModIntro.
  set versL' := drop (int.nat idx) versL.
  iExists versL'.
  iSplit; first eauto 10 with iFrame.
  iPureIntro.
  
  (**
   * Proving the postcondition.
   *)
  split; first apply sublist_drop.
  replace versL with (take (int.nat idx) versL ++ drop (int.nat idx) versL) by apply take_drop.
  apply Forall_app.
  split; apply Forall_forall.
  { (* Versions in the removed part have their end timestamps less than or equal `tid`. *)
    intros ver Hin Hgt.
    apply elem_of_list_lookup_1 in Hin as [i HSome].
    apply HidxOrder in HSome.
    lia.
  }
  { (* Versions in the remaining part are in the old list. *)
    intros ver Hin _.
    apply elem_of_list_lookup_1 in Hin as [i HSome].
    by apply elem_of_list_lookup_2 in HSome.
  }
Qed.

(*****************************************************************)
(* func (tuple *Tuple) RemoveVersions(tid uint64)                *)
(*                                                               *)
(* Notes:                                                        *)
(* 1. This method keeps all versions ending after [tid].         *)
(* 2. The precondition says that [tid] is less than or equal to  *)
(*    a lower bound of the minimal active tid.                   *)
(* 3. Call [txnMgr.getMinActiveTID] before calling this method.  *)
(*****************************************************************)
Theorem wp_tuple__RemoveVersions tuple (tid : u64) (key : u64) (tidlbN : nat) γ :
  is_tuple tuple key γ -∗
  {{{ min_tid_lb γ tidlbN ∗ ⌜(int.nat tid ≤ tidlbN)%nat⌝ }}}
    Tuple__RemoveVersions #tuple #tid
  {{{ RET #(); True }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> [HtidlbN %HtidN] HΦ".
  iNamed "Htuple".
  wp_call.
  
  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iDestruct "HtupleOwn" as (versL) "HtupleOwn".
  wp_pures.

  (***********************************************************)
  (* tuple.removeVersions(tid)                               *)
  (***********************************************************)
  wp_apply (wp_tuple__removeVersions with "HtupleOwn").
  iIntros "HtupleOwn".
  iDestruct "HtupleOwn" as (versL') "[HtupleOwn Hsafe]".
  
  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  { eauto 10 with iFrame. }
  wp_pures.
  by iApply "HΦ".
Qed.

(*****************************************************************)
(* func MkTuple() *Tuple                                         *)
(*****************************************************************)
Theorem wp_MkTuple (key : u64) γ :
  {{{ True }}}
    MkTuple #()
  {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.

  (***********************************************************)
  (* tuple := new(Tuple)                                     *)
  (***********************************************************)
  wp_apply (wp_allocStruct).
  { apply zero_val_ty'.
    simpl.
    repeat split.
  }
  iIntros (tuple) "Htuple".
  iDestruct (struct_fields_split with "Htuple") as "Htuple".
  iNamed "Htuple".
  simpl.
  wp_pures.
  
  (***********************************************************)
  (* tuple.latch = new(sync.Mutex)                           *)
  (***********************************************************)
  wp_apply (wp_new_free_lock).
  iIntros (latch) "Hfree".
  wp_storeField.
  
  (***********************************************************)
  (* tuple.rcond = sync.NewCond(tuple.latch)                 *)
  (***********************************************************)
  wp_loadField.
  wp_apply (wp_newCond' with "Hfree").
  iIntros (rcond) "[Hfree #HrcondC]".
  
  (***********************************************************)
  (* tuple.tidown = 0                                        *)
  (* tuple.tidrd = 0                                         *)
  (* tuple.tidwr = 0                                         *)
  (***********************************************************)
  repeat wp_storeField.
  
  (***********************************************************)
  (* tuple.vers = make([]Version, 0, 16)                     *)
  (***********************************************************)
  wp_apply (wp_new_slice); first auto.
  iIntros (vers) "HversL".
  wp_storeField.
  
  (***********************************************************)
  (* return tuple                                            *)
  (***********************************************************)
  iMod (alloc_lock mvccN _ latch (∃ versL, own_tuple tuple key versL γ) with "[$Hfree] [-latch rcond HΦ]") as "#Hlock".
  { iNext.
    iExists [].
    unfold own_tuple.
    do 5 iExists _.
    iFrame.
    admit.
  }
  iApply "HΦ".
  iExists latch, rcond.
  iMod (readonly_alloc_1 with "latch") as "$".
  iMod (readonly_alloc_1 with "rcond") as "$".
  by iFrame "#".
Admitted.

End heap.
